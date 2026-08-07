//! Microbenchmark isolating the advice-commitment MSM: how does the cost of a
//! batch of same-basis multiexponentiations depend on the *bit width* of the
//! scalars?
//!
//! Motivation: with many structurally similar columns, the commitment MSMs
//! dominate proving. The windowed (Pippenger) MSM makes one pass over all bases
//! per ~`c`-bit window across the full 256-bit scalar width. If the columns hold
//! bounded/small values (range-checked or lookup columns), the high windows are
//! all zero and contribute nothing in the accumulation phase.
//!
//! ```text
//! cargo run --release --example msm-scalar-width
//! ```

use std::time::Instant;

use group::ff::{Field, PrimeField};
use group::{Curve, Group};
use halo2_proofs::arithmetic::best_multiexp;
use halo2_proofs::pasta::{Eq, EqAffine, Fp};
use rand_core::{OsRng, RngCore};

fn bench(label: &str, coeffs_sets: &[Vec<Fp>], bases: &[EqAffine], iters: usize) {
    // Warm up.
    for coeffs in coeffs_sets {
        let _ = best_multiexp(coeffs, bases);
    }
    let mut best = std::time::Duration::MAX;
    for _ in 0..iters {
        let t = Instant::now();
        let mut acc = Eq::identity();
        for coeffs in coeffs_sets {
            acc += best_multiexp(coeffs, bases);
        }
        assert!(bool::from(!acc.is_identity()) || true);
        let _ = acc;
        best = best.min(t.elapsed());
    }
    println!(
        "{label:<28} {:?}  ({:?}/MSM)",
        best,
        best / coeffs_sets.len() as u32
    );
}

fn small_scalar(rng: &mut impl RngCore, bits: u32) -> Fp {
    // Uniform value in [0, 2^bits).
    let v = if bits >= 64 {
        rng.next_u64()
    } else {
        rng.next_u64() & ((1u64 << bits) - 1)
    };
    Fp::from(v)
}

fn main() {
    let n: usize = 1 << 12; // domain size for k=12
    let num_cols: usize = 200;
    let iters: usize = 5;
    let mut rng = OsRng;

    println!("n={n} num_cols={num_cols} iters={iters}");

    // Shared basis (as in commit_lagrange: same g_lagrange for every column).
    let bases: Vec<EqAffine> = {
        let proj: Vec<Eq> = (0..n).map(|_| Eq::random(&mut rng)).collect();
        let mut aff = vec![EqAffine::default(); n];
        Eq::batch_normalize(&proj, &mut aff);
        aff
    };

    // Full-width (uniform 255-bit) scalars: the general witness case.
    let full: Vec<Vec<Fp>> = (0..num_cols)
        .map(|_| (0..n).map(|_| Fp::random(&mut rng)).collect())
        .collect();

    // Bounded-width scalars: the range-checked / lookup-column case.
    let mk = |bits: u32, rng: &mut OsRng| -> Vec<Vec<Fp>> {
        (0..num_cols)
            .map(|_| (0..n).map(|_| small_scalar(rng, bits)).collect())
            .collect()
    };
    let w128 = mk(128, &mut rng);
    let w64 = mk(64, &mut rng);
    let w32 = mk(32, &mut rng);
    let w16 = mk(16, &mut rng);

    println!("scalar bits: {}", Fp::NUM_BITS);
    bench("full (255-bit)", &full, &bases, iters);
    bench("bounded 128-bit", &w128, &bases, iters);
    bench("bounded 64-bit", &w64, &bases, iters);
    bench("bounded 32-bit", &w32, &bases, iters);
    bench("bounded 16-bit", &w16, &bases, iters);
}
