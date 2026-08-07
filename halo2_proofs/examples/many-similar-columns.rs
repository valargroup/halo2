//! Benchmark harness for proving circuits with many structurally similar
//! advice columns at a small `k`.
//!
//! This models a common workload shape: a circuit whose cost is dominated by a
//! large number of advice columns that all share the same gate structure, at a
//! modest domain size (e.g. `k = 12`). At small `k` each individual per-column
//! FFT/MSM is tiny, so the interesting question is how well the prover exploits
//! the *across-column* parallelism.
//!
//! Run with (defaults: k=12, 200 columns, 5 iterations):
//!
//! ```text
//! cargo run --release --example many-similar-columns
//! K=12 COLS=200 ITERS=5 cargo run --release --example many-similar-columns
//! ```

use std::marker::PhantomData;
use std::time::Instant;

use group::ff::Field;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::plonk::*;
use halo2_proofs::poly::{commitment::Params, Rotation};
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use rand_core::OsRng;

#[derive(Clone)]
struct ManyColsConfig {
    advice: Vec<Column<Advice>>,
    selector: Column<Fixed>,
}

#[derive(Clone)]
struct ManyColsCircuit<F: Field> {
    seed: Value<F>,
    k: u32,
    num_cols: usize,
}

impl<F: Field> Circuit<F> for ManyColsCircuit<F> {
    type Config = ManyColsConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            seed: Value::unknown(),
            k: self.k,
            num_cols: self.num_cols,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> ManyColsConfig {
        let num_cols = std::env::var("COLS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(200usize);

        let advice: Vec<_> = (0..num_cols).map(|_| meta.advice_column()).collect();
        let selector = meta.fixed_column();

        // Every column gets the *same* structural gate: a squaring chain
        //   s * (w(cur)^2 - w(next)) = 0
        // This is degree 3, forcing a genuine extended-domain quotient FFT, and
        // is identical across all columns (the "structurally similar" shape).
        for &col in &advice {
            meta.create_gate("square-chain", |meta| {
                let s = meta.query_fixed(selector);
                let cur = meta.query_advice(col, Rotation::cur());
                let next = meta.query_advice(col, Rotation::next());
                vec![s * (cur.clone() * cur - next)]
            });
        }

        ManyColsConfig { advice, selector }
    }

    fn synthesize(
        &self,
        config: ManyColsConfig,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let n = 1usize << self.k;
        // Leave room for blinding rows.
        let usable = n - 10;

        layouter.assign_region(
            || "fill",
            |mut region| {
                // Enable the selector on all-but-last usable row.
                for row in 0..usable - 1 {
                    region.assign_fixed(|| "s", config.selector, row, || Value::known(F::ONE))?;
                }

                for &col in &config.advice {
                    let mut cur = self.seed;
                    for row in 0..usable {
                        region.assign_advice(|| "w", col, row, || cur)?;
                        cur = cur.map(|v| v.square());
                    }
                }
                Ok(())
            },
        )
    }
}

fn keygen(k: u32, num_cols: usize) -> (Params<EqAffine>, ProvingKey<EqAffine>) {
    let params: Params<EqAffine> = Params::new(k);
    let empty: ManyColsCircuit<Fp> = ManyColsCircuit {
        seed: Value::unknown(),
        k,
        num_cols,
    };
    let vk = keygen_vk(&params, &empty).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty).expect("keygen_pk should not fail");
    (params, pk)
}

fn prover(
    k: u32,
    num_cols: usize,
    params: &Params<EqAffine>,
    pk: &ProvingKey<EqAffine>,
) -> Vec<u8> {
    let rng = OsRng;
    let circuit: ManyColsCircuit<Fp> = ManyColsCircuit {
        seed: Value::known(Fp::random(rng)),
        k,
        num_cols,
    };
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(params, pk, &[circuit], &[&[]], rng, &mut transcript)
        .expect("proof generation should not fail");
    transcript.finalize()
}

fn main() {
    let k: u32 = std::env::var("K")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(12);
    let num_cols: usize = std::env::var("COLS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(200);
    let iters: usize = std::env::var("ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);

    let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into());
    println!("k={k} num_cols={num_cols} iters={iters} rayon_threads={threads}",);

    let t0 = Instant::now();
    let (params, pk) = keygen(k, num_cols);
    println!("keygen: {:?}", t0.elapsed());

    // Warm up (allocations, rayon pool spin-up).
    let proof = prover(k, num_cols, &params, &pk);
    println!("proof size: {} bytes", proof.len());

    // Verify correctness.
    let strategy = SingleVerifier::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(
        verify_proof(&params, pk.get_vk(), strategy, &[&[]], &mut transcript).is_ok(),
        "proof failed to verify"
    );
    println!("verify: OK");

    let mut best = std::time::Duration::MAX;
    let mut total = std::time::Duration::ZERO;
    for i in 0..iters {
        let t = Instant::now();
        let _ = prover(k, num_cols, &params, &pk);
        let e = t.elapsed();
        total += e;
        best = best.min(e);
        println!("iter {i}: {e:?}");
    }
    println!("best: {best:?}  avg: {:?}", total / iters as u32);

    let _ = PhantomData::<Fp>;
}
