//! End-to-end render coverage for the Vesta Lean fixture exporter.
//!
//! `plonk_api` cannot drive the exporter to completion: its `sa`/`sb` selectors are assigned
//! identically and its two proofs share public inputs, so the captured MSM merges those same-base
//! terms and the exporter's duplicate-base guard (correctly) rejects it. This test uses a small
//! circuit whose commitment bases are all distinct and non-identity, so `dump_vesta_lean_fixture`
//! runs to completion and we can assert the emitted accepting fixture. A companion test confirms
//! the exporter's identity fail-fast refuses a non-identity (rejecting) capture.
#![cfg(feature = "unstable-verifier-fingerprint")]

use group::ff::Field;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::plonk::fingerprint::{capture_proof_fingerprint, ChallengeRecorder};
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column, ConstraintSystem,
    Error, Instance, Selector, SingleVerifier, TableColumn,
};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::poly::Rotation;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use rand_core::OsRng;

const K: u32 = 5;

/// A minimal circuit exercising a custom gate, a permutation (via `constrain_instance`), and a
/// lookup — enough to drive every branch of the fixture exporter — while keeping every commitment
/// base distinct and non-identity so the exporter's duplicate-base guard is satisfied.
#[derive(Clone, Default)]
struct RenderCircuit {
    a: Value<Fp>,
    b: Value<Fp>,
}

#[derive(Clone)]
struct RenderConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    instance: Column<Instance>,
    s: Selector,
    table: TableColumn,
}

impl Circuit<Fp> for RenderCircuit {
    type Config = RenderConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> RenderConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let instance = meta.instance_column();
        let s = meta.selector();
        let table = meta.lookup_table_column();

        // Copy the product cell out to the instance column, so the circuit carries a permutation.
        meta.enable_equality(c);
        meta.enable_equality(instance);

        // A single multiplication gate: `s * (a * b - c) = 0`.
        meta.create_gate("mul", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let s = meta.query_selector(s);
            vec![s * (a * b - c)]
        });

        // Constrain the product into a small table. Halo2 excludes the blinding rows from the
        // lookup argument, so the unassigned (zero) product cells and the active product cell need
        // only appear in the table; the blinding rows may hold anything.
        meta.lookup(|meta| {
            let c = meta.query_advice(c, Rotation::cur());
            vec![(c, table)]
        });

        RenderConfig {
            a,
            b,
            c,
            instance,
            s,
            table,
        }
    }

    fn synthesize(
        &self,
        config: RenderConfig,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                for i in 0..8u64 {
                    table.assign_cell(
                        || "table row",
                        config.table,
                        i as usize,
                        || Value::known(Fp::from(i)),
                    )?;
                }
                Ok(())
            },
        )?;

        let c_cell = layouter.assign_region(
            || "mul",
            |mut region| {
                config.s.enable(&mut region, 0)?;
                region.assign_advice(|| "a", config.a, 0, || self.a)?;
                region.assign_advice(|| "b", config.b, 0, || self.b)?;
                region.assign_advice(|| "c = a * b", config.c, 0, || self.a * self.b)
            },
        )?;

        layouter.constrain_instance(c_cell.cell(), config.instance, 0)
    }
}

/// Build proving material and a single valid proof for `a * b`, returning the params, proving key,
/// the public product, and the proof bytes.
fn prove() -> (
    Params<EqAffine>,
    halo2_proofs::plonk::ProvingKey<EqAffine>,
    Fp,
    Vec<u8>,
) {
    let params: Params<EqAffine> = Params::new(K);

    let a = Fp::from(2);
    let b = Fp::from(3);
    let product = a * b; // 6, and in the lookup table `0..8`.

    let circuit = RenderCircuit {
        a: Value::known(a),
        b: Value::known(b),
    };

    // Sanity-check the circuit before proving, so a circuit bug surfaces clearly.
    let mock = MockProver::run(K, &circuit, vec![vec![product]]).expect("mock prover runs");
    assert_eq!(mock.verify(), Ok(()));

    let vk = keygen_vk(&params, &RenderCircuit::default()).expect("keygen_vk");
    let pk = keygen_pk(&params, vk, &RenderCircuit::default()).expect("keygen_pk");

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(
        &params,
        &pk,
        &[circuit],
        &[&[&[product]]],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation");
    let proof = transcript.finalize();

    (params, pk, product, proof)
}

#[test]
fn exports_accepting_fixture() {
    let (params, pk, product, proof) = prove();
    let pubinputs = vec![product];

    // The proof verifies, so the captured fingerprint is the group identity.
    let strategy = SingleVerifier::new(&params);
    let mut verify_transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof(
        &params,
        pk.get_vk(),
        strategy,
        &[&[&pubinputs[..]]],
        &mut verify_transcript,
    )
    .is_ok());

    let mut transcript = ChallengeRecorder::<_, _, Challenge255<_>>::init(&proof[..]);
    let msm =
        capture_proof_fingerprint(&params, pk.get_vk(), &[&[&pubinputs[..]]], &mut transcript)
            .expect("fingerprint capture");
    assert!(
        msm.clone().eval(),
        "a valid proof's fingerprint must be the identity"
    );

    let fixture = pk.get_vk().dump_vesta_lean_fixture(
        "Halo2.Fixture.Render",
        "render_accept",
        K,
        1,
        &transcript,
        &msm,
    );
    for expected in [
        "namespace Halo2.Fixture.Render",
        "def shape : Shape",
        "theorem capturedUrsG_length : capturedUrsG.length = 2 ^ shape.k",
        "def vk : VerifyingKey shape Fp G",
        "def ps : ProofString shape Fp G",
        "def ch : Challenges shape.k Fp",
        "def capturedMsm : Msm shape.k Fp G",
        "theorem fingerprint_matches",
        "theorem capturedMsm_eval_eq_zero",
        "theorem assembledMsm_eval_eq_zero",
        "end Halo2.Fixture.Render",
    ] {
        assert!(
            fixture.contains(expected),
            "accepting fixture is missing `{expected}`"
        );
    }
    // The accepting fixture must not carry a rejecting theorem.
    assert!(
        !fixture.contains("_ne_zero"),
        "accepting fixture must not emit a rejecting theorem"
    );
}

/// Only accepting runs are exported; a rejecting capture is checked in Rust and must be refused by
/// the exporter rather than emitted. Verify the same proof against the wrong public input: every
/// read still parses, so capture succeeds, but the assembled MSM is non-identity, so
/// `dump_vesta_lean_fixture`'s identity fail-fast rejects it.
#[test]
fn rejects_non_identity_capture() {
    let (params, pk, product, proof) = prove();
    let wrong_pubinputs = vec![product + Fp::ONE];

    let mut transcript = ChallengeRecorder::<_, _, Challenge255<_>>::init(&proof[..]);
    let msm = capture_proof_fingerprint(
        &params,
        pk.get_vk(),
        &[&[&wrong_pubinputs[..]]],
        &mut transcript,
    )
    .expect("fingerprint capture for a parseable rejecting proof");
    // The rejecting outcome is confirmed in Rust: the assembled MSM is non-identity.
    assert!(
        !msm.clone().eval(),
        "an invalid proof's fingerprint must be non-identity"
    );

    // Exporting it must fail fast on the identity check (its bases are distinct, so this is the
    // identity fail-fast, not the duplicate-base guard).
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let export_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        pk.get_vk().dump_vesta_lean_fixture(
            "Halo2.Fixture.RenderReject",
            "render_reject",
            K,
            1,
            &transcript,
            &msm,
        )
    }));
    std::panic::set_hook(prev_hook);
    let err = export_result.expect_err("exporter must refuse a non-identity capture");
    // The fail-fast is a plain `assert!` with a `&'static str` message, so the payload is `&str`
    // (not the `String` an `assert_eq!` with format args would produce).
    let panic_msg = err
        .downcast_ref::<&str>()
        .map(|s| (*s).to_owned())
        .or_else(|| err.downcast_ref::<String>().cloned())
        .expect("exporter fail-fast panics with a string message");
    assert!(
        panic_msg.contains("must evaluate to the identity"),
        "exporter panicked for an unexpected reason: {panic_msg}"
    );
}
