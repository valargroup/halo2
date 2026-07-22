//! Lean fixture export for the verifier-fingerprint match (dev/test tooling).
//!
//! [`VerifyingKey::dump_vesta_lean_fixture`] emits a self-contained Lean file in the requested namespace,
//! capturing one real proof: the verifying key (gates, query layouts, lookups, permutation
//! chunking, domain), the proof string, the Fiat-Shamir challenges, and the assembled MSM, plus the
//! `MsmMatch (assemble vk ps ch) capturedMsm := by native_decide` theorem.
//!
//! Scalar and base field elements are emitted as four little-endian `u64` limbs (`mkFp`/`mkFq`).
//! Commitments and the complete verifier URS are emitted as validated concrete Vesta points, shared
//! across the VK, proof string, transcript, and MSM.
//!
//! Trust boundary: the fixture attests that the assembled MSM matches, and evaluates to the
//! identity, for *these* captured commitments and challenges. It does not re-derive the instance
//! commitments from the public inputs (they enter as opaque points, like every other commitment),
//! nor does it reproduce Halo2's Blake2b transcript or pinned-key serialization; those remain
//! trusted from the Rust capture. Halo2's `MSM` also merges same-base terms and drops identity
//! bases, where the Lean assembly deliberately does neither; such a capture is rejected at export
//! (see [`VerifyingKey::dump_vesta_lean_fixture`]) rather than emitted.
//!
//! Only accepting runs are exported. [`VerifyingKey::dump_vesta_lean_fixture`] verifies the captured
//! MSM is the group identity before emitting anything, so every exported fixture proves
//! `capturedMsm.evalNat capturedURS = 0` and Lean checks exact MSM agreement against it. Invalid
//! captures are not modelled in Lean: they are rejected by the deployed verifier (or checked as
//! non-identity) in Rust, which is where the negative-path coverage lives. Exporting a rejecting
//! run as its own fixture was considered and dropped in favour of this fail-fast: it doubled the
//! exporter surface for a cross-check that a trivially-accepting Lean `assemble` would already fail
//! on the accepting fixtures.

use ff::PrimeField;
use std::collections::{BTreeSet, HashMap};
use std::io::Read;

use super::{ChallengeRecorder, TranscriptEvent};
use crate::arithmetic::{Coordinates, CurveAffine};
use crate::pasta::{EqAffine, Fp, Fq};
use crate::poly::commitment::MSM;
use crate::transcript::Challenge255;

use super::super::circuit::{Any, Expression};
use super::super::VerifyingKey;

/// A field element as a Lean constructor call with four little-endian `u64` limbs.
fn field<F: PrimeField>(constructor: &str, x: F) -> String {
    let repr = x.to_repr();
    let b = repr.as_ref();
    debug_assert!(
        b.len() <= 32,
        "field repr is wider than the four u64 limbs emitted here; extra bytes would be silently dropped"
    );
    let limb = |i: usize| -> u64 {
        let mut v: u64 = 0;
        let mut j = 0;
        while j < 8 {
            let idx = i * 8 + j;
            if idx < b.len() {
                v |= (b[idx] as u64) << (8 * j);
            }
            j += 1;
        }
        v
    };
    format!(
        "({} {} {} {} {})",
        constructor,
        limb(0),
        limb(1),
        limb(2),
        limb(3)
    )
}

/// A scalar field element as a Lean `mkFp` call (four little-endian `u64` limbs).
fn fp(x: Fp) -> String {
    field("mkFp", x)
}

/// A Vesta base-field element as a Lean `mkFq` call (four little-endian `u64` limbs).
fn fq(x: Fq) -> String {
    field("mkFq", x)
}

/// Whether `segment` is a conservative ASCII subset of a Lean identifier: non-empty, starting with a
/// letter or `_`, and otherwise containing only ASCII alphanumerics and `_`. A digit-leading segment
/// (e.g. `123`) is rejected, so a dotted `lean_namespace` spliced verbatim into `namespace`/`end`
/// cannot emit a token Lean would reject.
fn is_lean_ident(segment: &str) -> bool {
    let mut chars = segment.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Coordinate key for a point's identity (its affine `(x, y)` repr; identity → sentinel).
fn point_key(p: EqAffine) -> Vec<u8> {
    let co: Option<Coordinates<EqAffine>> = p.coordinates().into();
    match co {
        Some(c) => {
            let mut k = c.x().to_repr().as_ref().to_vec();
            k.extend_from_slice(c.y().to_repr().as_ref());
            k
        }
        None => vec![0u8],
    }
}

/// Deduplicated concrete curve points used by the generated Lean fixture. The generated terms have
/// type `VestaG`; the numeric indices are only source compression for repeated coordinate literals.
struct PointTable {
    ids: HashMap<Vec<u8>, usize>,
    points: Vec<EqAffine>,
}

impl PointTable {
    fn new() -> Self {
        Self {
            ids: HashMap::new(),
            points: Vec::new(),
        }
    }

    fn id(&mut self, point: EqAffine) -> usize {
        let key = point_key(point);
        if let Some(id) = self.ids.get(&key) {
            *id
        } else {
            let id = self.points.len();
            self.ids.insert(key, id);
            self.points.push(point);
            id
        }
    }

    fn point_ref(&mut self, point: EqAffine) -> String {
        format!("capturedPoint {}", self.id(point))
    }

    fn point_refs(&mut self, points: &[EqAffine]) -> Vec<String> {
        points.iter().map(|point| self.point_ref(*point)).collect()
    }

    fn coordinate_literals(&self) -> Vec<String> {
        self.points
            .iter()
            .map(|point| {
                let coordinates: Option<Coordinates<EqAffine>> = point.coordinates().into();
                match coordinates {
                    Some(coordinates) => {
                        format!("({}, {})", fq(*coordinates.x()), fq(*coordinates.y()))
                    }
                    None => "(0, 0)".to_string(),
                }
            })
            .collect()
    }
}

fn transcript_point(points: &mut PointTable, point: EqAffine) -> String {
    format!("TranscriptElt.point ({})", points.point_ref(point))
}

fn transcript_scalar(scalar: Fp) -> String {
    format!("TranscriptElt.scalar {}", fp(scalar))
}

fn join<T: ToString>(xs: &[T]) -> String {
    xs.iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

fn join_fps(xs: &[Fp]) -> String {
    xs.iter().map(|x| fp(*x)).collect::<Vec<_>>().join(", ")
}

/// Serialize one gate / lookup `Expression` to a Lean `Expr Fp` literal (mirrors the verifier's
/// `Expression::evaluate`; virtual selectors are removed before verification).
fn expr_to_lean(e: &Expression<Fp>) -> String {
    e.evaluate(
        &|c| format!("(.constant {})", fp(c)),
        &|_| panic!("virtual selectors are removed before verification"),
        &|q| format!("(.fixed {})", q.index),
        &|q| format!("(.advice {})", q.index),
        &|q| format!("(.instance {})", q.index),
        &|a: String| format!("(.negated {})", a),
        &|a: String, b: String| format!("(.sum {} {})", a, b),
        &|a: String, b: String| format!("(.product {} {})", a, b),
        &|a: String, c| format!("(.scaled {} {})", a, fp(c)),
    )
}

/// Render the typed transcript prefix and each subsequent squeeze checkpoint. `init_len` is the
/// exact number of VK/instance events that precede verifier proof processing; it is intentionally
/// independent of when the first proof element is read, because valid circuits may have no advice
/// commitments before the first squeeze.
fn render_transcript_capture(
    points: &mut PointTable,
    transcript_events: &[TranscriptEvent<EqAffine>],
    init_len: usize,
) -> (Vec<String>, Vec<String>) {
    let mut captured_init = Vec::new();
    let mut prefix = Vec::new();
    let mut schedule_entries = Vec::new();

    for (event_index, event) in transcript_events.iter().enumerate() {
        let is_init = event_index < init_len;
        match *event {
            TranscriptEvent::CommonPoint(point) => {
                let elt = transcript_point(points, point);
                if is_init {
                    captured_init.push(elt.clone());
                }
                prefix.push(elt);
            }
            TranscriptEvent::CommonScalar(scalar) => {
                let elt = transcript_scalar(scalar);
                if is_init {
                    captured_init.push(elt.clone());
                }
                prefix.push(elt);
            }
            TranscriptEvent::ReadPoint(point) => {
                assert!(
                    !is_init,
                    "proof read appeared inside the VK/instance prefix"
                );
                prefix.push(transcript_point(points, point));
            }
            TranscriptEvent::ReadScalar(scalar) => {
                assert!(
                    !is_init,
                    "proof read appeared inside the VK/instance prefix"
                );
                prefix.push(transcript_scalar(scalar));
            }
            TranscriptEvent::Squeeze(challenge) => {
                assert!(
                    !is_init,
                    "challenge squeeze appeared inside the VK/instance prefix"
                );
                schedule_entries.push(format!("([{}], {})", prefix.join(", "), fp(challenge)));
                prefix.push(transcript_scalar(challenge));
            }
        }
    }

    (captured_init, schedule_entries)
}

impl VerifyingKey<EqAffine> {
    /// Emit the Vesta Lean fixture for one captured proof (see module docs).
    ///
    /// `recorder` supplies the ordered transcript events, the proof elements (points and scalars in
    /// read order), the instance commitments, and the squeezed challenges captured during the
    /// verifier run; `captured_msm` is the assembled verifier fingerprint together with its exact
    /// parameter set. Only *accepting* runs are exported: `captured_msm` is verified to be the group
    /// identity before anything is emitted, so the fixture always proves `capturedMsm.evalNat = 0`.
    pub fn dump_vesta_lean_fixture<R: Read>(
        &self,
        lean_namespace: &str,
        circuit_id: &str,
        k: u32,
        num_proofs: usize,
        recorder: &ChallengeRecorder<R, EqAffine, Challenge255<EqAffine>>,
        captured_msm: &MSM<'_, EqAffine>,
    ) -> String {
        // `lean_namespace` is spliced verbatim into `namespace`/`end`, and `circuit_id` is emitted
        // via `{:?}`, whose Rust string escapes (`\u{...}`, ...) are not Lean's. Validate both up
        // front — in release builds too, since this runs once per export and a malformed name yields
        // an uncompilable fixture. [`is_lean_ident`] accepts a conservative ASCII subset of Lean
        // identifiers, so a digit-leading `lean_namespace` segment like `123` is rejected.
        assert!(
            lean_namespace.split('.').all(is_lean_ident),
            "lean_namespace must be a dot-separated path of ASCII Lean identifiers \
             (letter/underscore start): {lean_namespace:?}"
        );
        // `circuit_id` becomes a Lean *string literal*, not an identifier, so a leading digit is
        // fine; it only has to stay a plain ASCII slug so `{:?}` cannot emit a `\u{...}` escape Lean
        // would reject.
        assert!(
            !circuit_id.is_empty()
                && circuit_id
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'),
            "circuit_id must be a non-empty ASCII slug (alphanumeric, `_`, `-`): {circuit_id:?}"
        );

        let common_points = recorder.common_points.as_slice();
        let read_points = recorder.points.as_slice();
        let read_scalars = recorder.scalars.as_slice();
        let challenges = recorder.challenges.as_slice();
        let transcript_events = recorder.events.as_slice();

        let params = captured_msm.params;
        // The emitted `capturedMsm_eval_eq_zero` presupposes an accepting capture; fail fast here
        // rather than export a fixture whose theorem cannot hold. Rejecting captures are checked in
        // Rust (they are non-identity / rejected by the deployed verifier), never exported to Lean.
        assert!(
            captured_msm.clone().eval(),
            "captured MSM must evaluate to the identity; the emitted fixture proves it"
        );
        let (msm_g, msm_w, msm_u, msm_other) = captured_msm.fingerprint_terms();
        let msm_g = msm_g.expect("captured MSM must contain verifier-generator coefficients");
        let msm_w = msm_w.expect("captured MSM must contain a blinding-generator coefficient");
        let msm_u = msm_u.expect("captured MSM must contain an IPA-generator coefficient");
        let cs = &self.cs;
        let n_advice = cs.num_advice_columns;
        let n_inst_cols = cs.num_instance_columns;
        let n_lookups = cs.lookups.len();
        let chunk_len = self.cs_degree - 2;
        let perm_columns = cs.permutation.get_columns();
        // A zero chunk length is only consistent with there being no permutation columns; otherwise
        // `n_perm_sets` below and the chunk-export loop (which falls back to `chunk_len.max(1)`)
        // would disagree on how many sets exist.
        assert!(
            chunk_len > 0 || perm_columns.is_empty(),
            "permutation columns present but chunk length is zero"
        );
        let n_perm_sets = if chunk_len == 0 {
            0
        } else {
            perm_columns.chunks(chunk_len).count()
        };
        let n_perm_cols = self.permutation.commitments().len();
        let n_quotient = self.domain.get_quotient_poly_degree();
        let n_inst_q = cs.instance_queries.len();
        let n_adv_q = cs.advice_queries.len();
        let n_fixed_q = cs.fixed_queries.len();
        let blinding = cs.blinding_factors();
        let n: u64 = 1u64 << k;
        assert_eq!(params.k, k);
        assert_eq!(params.g.len(), n as usize);
        assert_eq!(msm_g.len(), n as usize);
        assert_eq!(common_points.len(), num_proofs * n_inst_cols);
        assert_eq!(challenges.len(), 11 + k as usize);

        let expected_read_points = num_proofs * n_advice
            + num_proofs * n_lookups * 2
            + num_proofs * n_perm_sets
            + num_proofs * n_lookups
            + 1
            + n_quotient
            + 1
            + 1
            + 2 * k as usize;
        assert_eq!(read_points.len(), expected_read_points);

        let minimum_read_scalars = num_proofs * n_inst_q
            + num_proofs * n_adv_q
            + n_fixed_q
            + 1
            + n_perm_cols
            + num_proofs
                * if n_perm_sets == 0 {
                    0
                } else {
                    3 * n_perm_sets - 1
                }
            + num_proofs * n_lookups * 5
            + 2;
        assert!(read_scalars.len() >= minimum_read_scalars);

        let event_common_points: Vec<_> = transcript_events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::CommonPoint(point) => Some(*point),
                _ => None,
            })
            .collect();
        let event_read_points: Vec<_> = transcript_events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::ReadPoint(point) => Some(*point),
                _ => None,
            })
            .collect();
        let event_read_scalars: Vec<_> = transcript_events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::ReadScalar(scalar) => Some(*scalar),
                _ => None,
            })
            .collect();
        let event_challenges: Vec<_> = transcript_events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::Squeeze(challenge) => Some(*challenge),
                _ => None,
            })
            .collect();
        assert_eq!(event_common_points, common_points);
        assert_eq!(event_read_points, read_points);
        assert_eq!(event_read_scalars, read_scalars);
        assert_eq!(event_challenges, challenges);

        let transcript_init_len = 1 + common_points.len();
        assert!(transcript_events.len() >= transcript_init_len);
        assert!(matches!(
            transcript_events.first(),
            Some(TranscriptEvent::CommonScalar(scalar)) if *scalar == self.transcript_repr
        ));
        for (event, expected_point) in transcript_events[1..transcript_init_len]
            .iter()
            .zip(common_points)
        {
            assert!(matches!(
                event,
                TranscriptEvent::CommonPoint(point) if point == expected_point
            ));
        }

        let mut points = PointTable::new();
        let urs_g = points.point_refs(&params.g);
        let urs_w = points.point_ref(params.w);
        let urs_u = points.point_ref(params.u);

        // The blocks below are a hand-maintained mirror of the verifier's read schedule; the
        // count asserts alone cannot catch an equal-length reordering. The Fiat-Shamir squeezes
        // delimit each phase of that schedule, so recover how many points/scalars had been read
        // before each squeeze and pin every block boundary that a squeeze delimits against it.
        // The challenges are, in squeeze order: θ, β, γ, y, x, x1, x2, x3, x4, ξ, z, then one per
        // IPA round.
        let (points_before_squeeze, scalars_before_squeeze): (Vec<usize>, Vec<usize>) = {
            let mut points_at = Vec::with_capacity(challenges.len());
            let mut scalars_at = Vec::with_capacity(challenges.len());
            let (mut np, mut ns) = (0usize, 0usize);
            for event in transcript_events {
                match event {
                    TranscriptEvent::ReadPoint(_) => np += 1,
                    TranscriptEvent::ReadScalar(_) => ns += 1,
                    TranscriptEvent::Squeeze(_) => {
                        points_at.push(np);
                        scalars_at.push(ns);
                    }
                    _ => {}
                }
            }
            (points_at, scalars_at)
        };
        assert_eq!(points_before_squeeze.len(), challenges.len());
        // Squeeze indices into the challenge/`*_before_squeeze` vectors.
        const THETA: usize = 0;
        const BETA: usize = 1;
        const GAMMA: usize = 2;
        const Y: usize = 3;
        const X: usize = 4;
        const X1: usize = 5;
        const X2: usize = 6;
        const X3: usize = 7;
        const X4: usize = 8;
        const XI: usize = 9;
        const Z: usize = 10;
        const IPA_ROUND_BASE: usize = 11;

        // ---- slice read points into blocks (verifier read order), pinning each squeeze-delimited
        //      boundary against `points_before_squeeze` ----
        let mut pi = 0usize;
        let advice_pts = &read_points[pi..pi + num_proofs * n_advice];
        pi += num_proofs * n_advice;
        // θ is squeezed once all advice commitments have been read.
        assert_eq!(pi, points_before_squeeze[THETA]);
        let lookup_perm_pts = &read_points[pi..pi + num_proofs * n_lookups * 2];
        pi += num_proofs * n_lookups * 2;
        // β, then γ with no reads between them, follow the lookup permuted commitments.
        assert_eq!(pi, points_before_squeeze[BETA]);
        assert_eq!(points_before_squeeze[GAMMA], points_before_squeeze[BETA]);
        let perm_prod_pts = &read_points[pi..pi + num_proofs * n_perm_sets];
        pi += num_proofs * n_perm_sets;
        let lookup_prod_pts = &read_points[pi..pi + num_proofs * n_lookups];
        pi += num_proofs * n_lookups;
        let vanishing_random = read_points[pi];
        pi += 1;
        // y is squeezed after the permutation/lookup products and the pre-y vanishing commitment.
        assert_eq!(pi, points_before_squeeze[Y]);
        let h_pts = &read_points[pi..pi + n_quotient];
        pi += n_quotient;
        // x is squeezed after the quotient (h) pieces; x1 and x2 follow with no points between.
        assert_eq!(pi, points_before_squeeze[X]);
        assert_eq!(points_before_squeeze[X1], points_before_squeeze[X]);
        assert_eq!(points_before_squeeze[X2], points_before_squeeze[X]);
        let q_prime = read_points[pi];
        pi += 1;
        // x3 is squeezed after q'; x4 follows with no points between (only the multiopen u scalars).
        assert_eq!(pi, points_before_squeeze[X3]);
        assert_eq!(points_before_squeeze[X4], points_before_squeeze[X3]);
        let ipa_s = read_points[pi];
        pi += 1;
        // ξ is squeezed after the IPA s commitment; z follows with no reads between.
        assert_eq!(pi, points_before_squeeze[XI]);
        assert_eq!(points_before_squeeze[Z], points_before_squeeze[XI]);
        let ipa_round_pts = &read_points[pi..]; // 2*k points (L, R per round)
        assert_eq!(ipa_round_pts.len(), 2 * k as usize);
        // Each IPA round reads its (L, R) pair immediately before squeezing that round's challenge.
        for round in 0..k as usize {
            assert_eq!(
                points_before_squeeze[IPA_ROUND_BASE + round],
                pi + 2 * (round + 1)
            );
        }

        // ---- slice read scalars into blocks, pinning each squeeze-delimited boundary against
        //      `scalars_before_squeeze` ----
        let mut si = 0usize;
        let instance_evals = &read_scalars[si..si + num_proofs * n_inst_q];
        si += num_proofs * n_inst_q;
        let advice_evals = &read_scalars[si..si + num_proofs * n_adv_q];
        si += num_proofs * n_adv_q;
        let fixed_evals = &read_scalars[si..si + n_fixed_q];
        si += n_fixed_q;
        let vanishing_eval = read_scalars[si];
        si += 1;
        let perm_common = &read_scalars[si..si + n_perm_cols];
        si += n_perm_cols;
        let perm_set_count = if n_perm_sets == 0 {
            0
        } else {
            3 * n_perm_sets - 1
        };
        let perm_set_evals = &read_scalars[si..si + num_proofs * perm_set_count];
        si += num_proofs * perm_set_count;
        let lookup_evals = &read_scalars[si..si + num_proofs * n_lookups * 5];
        si += num_proofs * n_lookups * 5;
        // All evaluations at x are read before x1 is squeezed; x2 and x3 follow with no scalars
        // between them (only the q' point read).
        assert_eq!(si, scalars_before_squeeze[X1]);
        assert_eq!(scalars_before_squeeze[X2], scalars_before_squeeze[X1]);
        assert_eq!(scalars_before_squeeze[X3], scalars_before_squeeze[X1]);
        assert!(read_scalars.len() >= si + 2);
        let n_point_sets = read_scalars.len() - 2 - si;
        let multiopen_u = &read_scalars[si..si + n_point_sets];
        si += n_point_sets;
        // x4 is squeezed after the multiopen u-evaluations; ξ, z, and every IPA-round squeeze then
        // precede the final c/f scalars, which are read only after the last squeeze.
        assert_eq!(si, scalars_before_squeeze[X4]);
        assert_eq!(scalars_before_squeeze[XI], si);
        assert_eq!(scalars_before_squeeze[Z], si);
        for round in 0..k as usize {
            assert_eq!(scalars_before_squeeze[IPA_ROUND_BASE + round], si);
        }
        let ipa_c = read_scalars[si];
        let ipa_f = read_scalars[si + 1];
        assert_eq!(si + 2, read_scalars.len());

        // ---- fail fast if the capture cannot possibly match in Lean ----
        //
        // Halo2's `MSM` keys terms by base coordinate and drops the identity, whereas the Lean
        // `assemble` appends one `other` term per protocol commitment slot and keeps every one. So
        // if two distinct slots share a base coordinate (e.g. two identically-assigned fixed
        // columns, or two proofs with equal instance commitments), or any slot is the identity, the
        // captured MSM carries strictly fewer `other` terms than `assemble`, and `fingerprint_matches`
        // — a permutation comparison with no merging — cannot hold. Diagnose that here instead of
        // deferring to an opaque Lean failure on a fixture that can never be discharged.
        //
        // The base slots are reconstructed from the same query layout the verifier consumes: one
        // slot per (proof, distinct queried instance/advice column), one per queried fixed column,
        // one per permutation-common / permutation-product / lookup / quotient (`h`) piece
        // commitment, plus the vanishing-random commitment, `q'`, the IPA `s`, and each IPA `L`/`R`.
        let distinct = |mut cols: Vec<usize>| {
            cols.sort_unstable();
            cols.dedup();
            cols
        };
        let inst_cols = distinct(cs.instance_queries.iter().map(|(c, _)| c.index()).collect());
        let adv_cols = distinct(cs.advice_queries.iter().map(|(c, _)| c.index()).collect());
        let fix_cols = distinct(cs.fixed_queries.iter().map(|(c, _)| c.index()).collect());
        let mut msm_base_slots: Vec<EqAffine> = Vec::new();
        for p in 0..num_proofs {
            for &col in &inst_cols {
                msm_base_slots.push(common_points[p * n_inst_cols + col]);
            }
            for &col in &adv_cols {
                msm_base_slots.push(advice_pts[p * n_advice + col]);
            }
        }
        for &col in &fix_cols {
            msm_base_slots.push(self.fixed_commitments[col]);
        }
        msm_base_slots.extend_from_slice(self.permutation.commitments());
        msm_base_slots.extend_from_slice(perm_prod_pts);
        msm_base_slots.extend_from_slice(lookup_perm_pts);
        msm_base_slots.extend_from_slice(lookup_prod_pts);
        msm_base_slots.push(vanishing_random);
        msm_base_slots.extend_from_slice(h_pts);
        msm_base_slots.push(q_prime);
        msm_base_slots.push(ipa_s);
        msm_base_slots.extend_from_slice(ipa_round_pts);

        let slot_coords: BTreeSet<Vec<u8>> = msm_base_slots
            .iter()
            .filter_map(|point| {
                let coords: Option<Coordinates<EqAffine>> = point.coordinates().into();
                // Halo2 drops the identity from the MSM, so it is not a captured base coordinate.
                coords.map(|_| point_key(*point))
            })
            .collect();
        let captured_coords: BTreeSet<Vec<u8>> = msm_other
            .iter()
            .map(|(_, x, y)| {
                let point: Option<EqAffine> = EqAffine::from_xy(*x, *y).into();
                point_key(point.expect("captured MSM base must be a valid affine point"))
            })
            .collect();
        // Self-check: the reconstructed slot bases must reproduce the captured MSM's actual bases.
        // A mismatch means the verifier read/query schedule assumed above has drifted from the
        // deployed verifier, so the reconstruction (and the guard below) can no longer be trusted.
        assert_eq!(
            slot_coords, captured_coords,
            "exporter's MSM base-slot reconstruction does not match the captured MSM bases; the \
             assumed verifier read/query schedule is stale"
        );
        // The guard: with all-distinct, non-identity bases the slot count equals the captured term
        // count. Any shortfall means Halo2 merged same-base terms or dropped an identity base.
        assert_eq!(
            msm_base_slots.len(),
            msm_other.len(),
            "captured MSM collapsed {} protocol commitment slots into {} terms by merging same-base \
             terms or dropping identity bases; the Lean assembly does neither, so the emitted \
             `fingerprint_matches` could not hold. Capture a proof whose commitments are all \
             distinct and non-identity.",
            msm_base_slots.len(),
            msm_other.len()
        );

        let mut out = String::new();

        // ---- Shape ----
        out.push_str(&format!(
            "def shape : Shape := {{ k := {}, numProofs := {}, numAdviceColumns := {}, numLookups := {}, numPermutationSets := {}, numPermutationColumns := {}, numQuotientPieces := {}, numInstanceQueries := {}, numAdviceQueries := {}, numFixedQueries := {}, numPointSets := {} }}\n\n",
            k, num_proofs, n_advice, n_lookups, n_perm_sets, n_perm_cols, n_quotient, n_inst_q, n_adv_q, n_fixed_q, n_point_sets,
        ));
        out.push_str(&format!(
            "def capturedUrsG : List G := [{}]\n\n",
            urs_g.join(", ")
        ));
        out.push_str(&format!(
            "def capturedURS : URS G := {{ k := {}, g := fun i => capturedUrsG.getD i.val 0, w := {}, u := {} }}\n\n",
            k, urs_w, urs_u
        ));
        // `capturedURS.g` indexes `capturedUrsG` with `getD`, which silently yields the identity for
        // any index past the list's end; pin the length so a truncated URS cannot pass unnoticed.
        out.push_str(
            "/-- The captured URS lists exactly the `2 ^ k` generators the MSM evaluates\n",
        );
        out.push_str("against, so `capturedURS.g`'s `getD` never substitutes the identity for a\n");
        out.push_str("missing generator. -/\n");
        out.push_str("theorem capturedUrsG_length : capturedUrsG.length = 2 ^ shape.k := by native_decide\n\n");
        out.push_str(&format!(
            "def capturedVkTranscriptRepr : Fp := {}\n\n",
            fp(self.transcript_repr)
        ));

        // ---- gates ----
        let gates: Vec<String> = cs
            .gates
            .iter()
            .flat_map(|g| g.polynomials().iter().map(expr_to_lean))
            .collect();

        // ---- query layouts ----
        let inst_layout: Vec<String> = cs
            .instance_queries
            .iter()
            .map(|(c, r)| format!("({}, ({} : ℤ))", c.index(), r.0))
            .collect();
        let adv_layout: Vec<String> = cs
            .advice_queries
            .iter()
            .map(|(c, r)| format!("({}, ({} : ℤ))", c.index(), r.0))
            .collect();
        let fix_layout: Vec<String> = cs
            .fixed_queries
            .iter()
            .map(|(c, r)| format!("({}, ({} : ℤ))", c.index(), r.0))
            .collect();

        // ---- permutation chunks: (ColumnRef × ℕ common-eval index) ----
        let mut chunks: Vec<String> = Vec::new();
        let mut gidx = 0usize;
        for chunk in perm_columns.chunks(chunk_len.max(1)) {
            let mut entries: Vec<String> = Vec::new();
            for col in chunk {
                let qi = cs.get_any_query_index(*col);
                let cref = match col.column_type() {
                    Any::Advice => format!("(.advice {})", qi),
                    Any::Fixed => format!("(.fixed {})", qi),
                    Any::Instance => format!("(.instance {})", qi),
                };
                entries.push(format!("({}, {})", cref, gidx));
                gidx += 1;
            }
            chunks.push(format!("[{}]", entries.join(", ")));
        }

        // ---- lookup input/table expressions ----
        let lk_in: Vec<String> = cs
            .lookups
            .iter()
            .map(|a| {
                format!(
                    "[{}]",
                    a.input_expressions
                        .iter()
                        .map(expr_to_lean)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect();
        let lk_tab: Vec<String> = cs
            .lookups
            .iter()
            .map(|a| {
                format!(
                    "[{}]",
                    a.table_expressions
                        .iter()
                        .map(expr_to_lean)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect();

        // ---- VK commitments as concrete Vesta point references ----
        let fixed_points = points.point_refs(&self.fixed_commitments);
        let inst_comm_points = points.point_refs(common_points);
        let perm_comm_points = points.point_refs(self.permutation.commitments());

        out.push_str(&format!(
            "def capturedNumInstanceColumns : ℕ := {}\n\n",
            n_inst_cols
        ));
        out.push_str(&format!(
            "def capturedFixedCommitments : List G := [{}]\n\n",
            join(&fixed_points)
        ));
        out.push_str(&format!(
            "def capturedInstanceCommitments : List G := [{}]\n\n",
            join(&inst_comm_points)
        ));
        out.push_str(&format!(
            "def capturedPermutationCommonCommitments : List G := [{}]\n\n",
            join(&perm_comm_points)
        ));

        out.push_str("def vk : VerifyingKey shape Fp G := {\n");
        out.push_str(&format!("  omega := {},\n", fp(self.domain.get_omega())));
        out.push_str(&format!("  n := {},\n", n));
        out.push_str(&format!("  blindingFactors := {},\n", blinding));
        out.push_str(&format!("  delta := {},\n", fp(Fp::DELTA)));
        out.push_str(&format!("  chunkLen := {},\n", chunk_len));
        out.push_str(&format!("  gates := [{}],\n", gates.join(", ")));
        out.push_str(&format!(
            "  instanceQueryLayout := [{}],\n",
            inst_layout.join(", ")
        ));
        out.push_str(&format!(
            "  adviceQueryLayout := [{}],\n",
            adv_layout.join(", ")
        ));
        out.push_str(&format!(
            "  fixedQueryLayout := [{}],\n",
            fix_layout.join(", ")
        ));
        out.push_str("  fixedCommitment := fun i => capturedFixedCommitments.getD i 0,\n");
        out.push_str("  instanceCommitment := fun p i => capturedInstanceCommitments.getD (p.val * capturedNumInstanceColumns + i) 0,\n");
        out.push_str("  permutationCommonCommitment := fun i => capturedPermutationCommonCommitments.getD i.val 0,\n");
        out.push_str(&format!(
            "  permutationChunks := [{}],\n",
            chunks.join(", ")
        ));
        out.push_str(&format!(
            "  lookupInputExprs := fun l => ([{}] : List (List (Expr Fp))).getD l.val [],\n",
            lk_in.join(", ")
        ));
        out.push_str(&format!(
            "  lookupTableExprs := fun l => ([{}] : List (List (Expr Fp))).getD l.val [] }}\n\n",
            lk_tab.join(", ")
        ));

        // ---- proof string ----
        let advice_points = points.point_refs(advice_pts);
        let lk_input_points: Vec<String> = (0..num_proofs * n_lookups)
            .map(|i| points.point_ref(lookup_perm_pts[i * 2]))
            .collect();
        let lk_table_points: Vec<String> = (0..num_proofs * n_lookups)
            .map(|i| points.point_ref(lookup_perm_pts[i * 2 + 1]))
            .collect();
        let perm_prod_points = points.point_refs(perm_prod_pts);
        let lk_prod_points = points.point_refs(lookup_prod_pts);
        let h_points = points.point_refs(h_pts);
        let vanishing_random_point = points.point_ref(vanishing_random);
        let q_prime_point = points.point_ref(q_prime);
        let ipa_s_point = points.point_ref(ipa_s);
        let ipa_round_ids: Vec<String> = (0..ipa_round_pts.len() / 2)
            .map(|j| {
                format!(
                    "({}, {})",
                    points.point_ref(ipa_round_pts[2 * j]),
                    points.point_ref(ipa_round_pts[2 * j + 1])
                )
            })
            .collect();

        // permutation set evals: walk per proof / per set (eval, next, [last])
        let mut perm_set_lits: Vec<String> = Vec::new();
        {
            let mut idx = 0usize;
            for _p in 0..num_proofs {
                for s in 0..n_perm_sets {
                    let eval = perm_set_evals[idx];
                    idx += 1;
                    let next = perm_set_evals[idx];
                    idx += 1;
                    let last = if s + 1 < n_perm_sets {
                        let l = perm_set_evals[idx];
                        idx += 1;
                        format!("some {}", fp(l))
                    } else {
                        "none".to_string()
                    };
                    perm_set_lits.push(format!(
                        "{{ eval := {}, nextEval := {}, lastEval := {} }}",
                        fp(eval),
                        fp(next),
                        last
                    ));
                }
            }
        }
        let lookup_lits: Vec<String> = (0..num_proofs * n_lookups).map(|i| {
            let b = i * 5;
            format!("{{ productEval := {}, productNextEval := {}, permutedInputEval := {}, permutedInputInvEval := {}, permutedTableEval := {} }}",
                fp(lookup_evals[b]), fp(lookup_evals[b + 1]), fp(lookup_evals[b + 2]), fp(lookup_evals[b + 3]), fp(lookup_evals[b + 4]))
        }).collect();

        out.push_str(&format!(
            "def capturedAdviceCommitments : List G := [{}]\n\n",
            join(&advice_points)
        ));
        out.push_str(&format!(
            "def capturedLookupPermutedInput : List G := [{}]\n\n",
            join(&lk_input_points)
        ));
        out.push_str(&format!(
            "def capturedLookupPermutedTable : List G := [{}]\n\n",
            join(&lk_table_points)
        ));
        out.push_str(&format!(
            "def capturedPermutationProducts : List G := [{}]\n\n",
            join(&perm_prod_points)
        ));
        out.push_str(&format!(
            "def capturedLookupProducts : List G := [{}]\n\n",
            join(&lk_prod_points)
        ));
        out.push_str(&format!(
            "def capturedHPieces : List G := [{}]\n\n",
            join(&h_points)
        ));
        out.push_str(&format!(
            "def capturedInstanceEvals : List Fp := [{}]\n\n",
            join_fps(instance_evals)
        ));
        out.push_str(&format!(
            "def capturedAdviceEvals : List Fp := [{}]\n\n",
            join_fps(advice_evals)
        ));
        out.push_str(&format!(
            "def capturedFixedEvals : List Fp := [{}]\n\n",
            join_fps(fixed_evals)
        ));
        out.push_str(&format!(
            "def capturedPermutationCommonEvals : List Fp := [{}]\n\n",
            join_fps(perm_common)
        ));
        out.push_str(&format!(
            "def capturedPermutationSetEvals : List (PermSetEval Fp) := [{}]\n\n",
            perm_set_lits.join(", ")
        ));
        out.push_str(&format!(
            "def capturedLookupEvals : List (LookupEval Fp) := [{}]\n\n",
            lookup_lits.join(", ")
        ));
        out.push_str(&format!(
            "def capturedMultiopenU : List Fp := [{}]\n\n",
            join_fps(multiopen_u)
        ));
        out.push_str(&format!(
            "def capturedIpaRounds : List (G × G) := [{}]\n\n",
            ipa_round_ids.join(", ")
        ));

        out.push_str("def ps : ProofString shape Fp G := {\n");
        out.push_str(&format!("  adviceCommitments := fun p c => capturedAdviceCommitments.getD (p.val * {} + c.val) 0,\n", n_advice));
        out.push_str(&format!("  lookupPermutedInput := fun p l => capturedLookupPermutedInput.getD (p.val * {} + l.val) 0,\n", n_lookups));
        out.push_str(&format!("  lookupPermutedTable := fun p l => capturedLookupPermutedTable.getD (p.val * {} + l.val) 0,\n", n_lookups));
        out.push_str(&format!("  permutationProduct := fun p s => capturedPermutationProducts.getD (p.val * {} + s.val) 0,\n", n_perm_sets));
        out.push_str(&format!(
            "  lookupProduct := fun p l => capturedLookupProducts.getD (p.val * {} + l.val) 0,\n",
            n_lookups
        ));
        out.push_str(&format!(
            "  vanishingRandom := {},\n",
            vanishing_random_point
        ));
        out.push_str("  hPieces := fun i => capturedHPieces.getD i.val 0,\n");
        out.push_str(&format!(
            "  instanceEvals := fun p q => capturedInstanceEvals.getD (p.val * {} + q.val) 0,\n",
            n_inst_q
        ));
        out.push_str(&format!(
            "  adviceEvals := fun p q => capturedAdviceEvals.getD (p.val * {} + q.val) 0,\n",
            n_adv_q
        ));
        out.push_str("  fixedEvals := fun q => capturedFixedEvals.getD q.val 0,\n");
        out.push_str(&format!(
            "  vanishingRandomEval := {},\n",
            fp(vanishing_eval)
        ));
        out.push_str(
            "  permutationCommonEvals := fun i => capturedPermutationCommonEvals.getD i.val 0,\n",
        );
        out.push_str(&format!("  permutationSetEvals := fun p s => capturedPermutationSetEvals.getD (p.val * {} + s.val) {{ eval := 0, nextEval := 0, lastEval := none }},\n", n_perm_sets));
        out.push_str(&format!("  lookupEvals := fun p l => capturedLookupEvals.getD (p.val * {} + l.val) {{ productEval := 0, productNextEval := 0, permutedInputEval := 0, permutedInputInvEval := 0, permutedTableEval := 0 }},\n", n_lookups));
        out.push_str(&format!("  multiopenQPrime := {},\n", q_prime_point));
        out.push_str("  multiopenU := fun s => capturedMultiopenU.getD s.val 0,\n");
        out.push_str(&format!("  ipaS := {},\n", ipa_s_point));
        out.push_str("  ipaRounds := fun j => capturedIpaRounds.getD j.val (0, 0),\n");
        out.push_str(&format!("  ipaC := {},\n", fp(ipa_c)));
        out.push_str(&format!("  ipaF := {} }}\n\n", fp(ipa_f)));

        // ---- challenges ----
        let ipa_ch: Vec<Fp> = challenges[11..].to_vec();
        out.push_str("def ch : Challenges shape.k Fp := {\n");
        out.push_str(&format!(
            "  theta := {}, beta := {}, gamma := {}, y := {}, x := {},\n",
            fp(challenges[0]),
            fp(challenges[1]),
            fp(challenges[2]),
            fp(challenges[3]),
            fp(challenges[4])
        ));
        out.push_str(&format!(
            "  x1 := {}, x2 := {}, x3 := {}, x4 := {},\n",
            fp(challenges[5]),
            fp(challenges[6]),
            fp(challenges[7]),
            fp(challenges[8])
        ));
        out.push_str(&format!(
            "  xi := {}, z := {},\n",
            fp(challenges[9]),
            fp(challenges[10])
        ));
        out.push_str(&format!(
            "  ipaRound := fun j => ([{}] : List Fp).getD j.val 0 }}\n\n",
            join_fps(&ipa_ch)
        ));

        // ---- captured Fiat-Shamir prelude and schedule ----
        //
        // The recorder observes the full typed deployed transcript after Blake2b initialization:
        // the verification-key transcript scalar, instance commitments, proof reads, and squeezes.
        // `capturedInit` contains the exact VK/instance prefix. After each later squeeze we append
        // the captured challenge as a scalar because `deriveChallenges` uses that abstract separator
        // between consecutive squeezes; the deployed Blake2b transcript instead uses a domain-prefix
        // byte.
        let (captured_init, schedule_entries) =
            render_transcript_capture(&mut points, transcript_events, transcript_init_len);
        out.push_str("/-- Captured verifier Fiat-Shamir prefix before the proof-derived transcript suffix.\n");
        out.push_str("Generated from `ChallengeRecorder`'s verification-key and instance absorb events. -/\n");
        out.push_str("def capturedInit : List (TranscriptElt Fp G) :=\n");
        out.push_str(&format!("  [{}]\n\n", captured_init.join(", ")));
        out.push_str("theorem capturedInit_startsWith_vkTranscriptRepr :\n");
        out.push_str("    capturedInit.head? = some (TranscriptElt.scalar capturedVkTranscriptRepr) := by native_decide\n\n");
        out.push_str(
            "/-- Captured verifier Fiat-Shamir schedule, including the captured prefix.\n",
        );
        out.push_str(
            "Generated from `ChallengeRecorder`'s ordered absorb/squeeze events. After each\n",
        );
        out.push_str(
            "squeeze the captured challenge is appended as an abstract separator (mirroring\n",
        );
        out.push_str(
            "`deriveChallenges`); the deployed Blake2b transcript uses a domain-prefix byte. -/\n",
        );
        out.push_str("def capturedScheduleEntries : List (List (TranscriptElt Fp G) × Fp) :=\n");
        out.push_str(&format!("  [{}]\n\n", schedule_entries.join(", ")));

        // ---- captured MSM ----
        let other_lits: Vec<String> = msm_other
            .iter()
            .map(|(s, x, y)| {
                let point: Option<EqAffine> = EqAffine::from_xy(*x, *y).into();
                let point = point.expect("captured MSM base must be a valid affine point");
                format!("({}, {})", fp(*s), points.point_ref(point))
            })
            .collect();
        out.push_str("def capturedMsm : Msm shape.k Fp G := {\n");
        out.push_str(&format!(
            "  gScalars := fun i => (#[{}] : Array Fp)[i.val]!,\n",
            join_fps(&msm_g)
        ));
        out.push_str(&format!("  wScalar := {},\n", fp(msm_w)));
        out.push_str(&format!("  uScalar := {},\n", fp(msm_u)));
        out.push_str(&format!("  other := [{}] }}\n\n", other_lits.join(", ")));

        out.push_str("theorem fingerprint_matches : MsmMatch (assemble vk ps ch) capturedMsm := by native_decide\n\n");
        out.push_str("theorem capturedMsm_eval_eq_zero : capturedMsm.evalNat capturedURS = 0 := by native_decide\n\n");
        out.push_str(
            "/-- Meaningful jointly with `fingerprint_matches`: `assemble`'s zero-MSM rejection\n",
        );
        out.push_str(
            "fallback also evaluates to zero, so this statement alone is not acceptance. -/\n",
        );
        out.push_str("theorem assembledMsm_eval_eq_zero : (assemble vk ps ch).evalNat capturedURS = 0 := by\n");
        out.push_str("  rw [msmMatch_evalNat capturedURS fingerprint_matches]\n");
        out.push_str("  exact capturedMsm_eval_eq_zero\n\n");
        out.push_str(&format!("end {}\n", lean_namespace));

        let body = out;
        let point_coordinates = points.coordinate_literals();
        let mut out = String::new();
        out.push_str(
            "-- Auto-generated by halo2 `dump_vesta_lean_fixture`. Do not edit by hand.\n",
        );
        // `maxRecDepth` is raised for the deeply-nested literals (the 2048-element URS and
        // g-scalar arrays, point-coordinate validation, and gate Expr trees) that `native_decide`
        // compiles.
        out.push_str(&format!(
            "import Zcash.Snark\n\nset_option maxRecDepth 1000000\n\nnamespace {}\n\nopen Zcash.Snark\nopen CompElliptic.CurveForms.ShortWeierstrass\nopen CompElliptic.Curves.Pasta\nopen CompElliptic.Fields.Pasta\n\n",
            lean_namespace
        ));
        out.push_str("/-- Scalar field element from four little-endian u64 limbs. -/\n");
        out.push_str("def mkFp (a b c d : ℕ) : Fp := (a : Fp) + (b : Fp) * (2 : Fp) ^ 64 + (c : Fp) * (2 : Fp) ^ 128 + (d : Fp) * (2 : Fp) ^ 192\n\n");
        out.push_str("abbrev Fq := VestaBaseField\n\n");
        out.push_str("/-- Vesta base field element from four little-endian u64 limbs. -/\n");
        out.push_str("def mkFq (a b c d : ℕ) : Fq := (a : Fq) + (b : Fq) * (2 : Fq) ^ 64 + (c : Fq) * (2 : Fq) ^ 128 + (d : Fq) * (2 : Fq) ^ 192\n\n");
        out.push_str("abbrev G := VestaG\n\n");
        out.push_str("instance : Inhabited G := ⟨0⟩\n\n");
        out.push_str(&format!(
            "def capturedCircuitId : String := {:?}\n\n",
            circuit_id
        ));
        out.push_str("/-- Canonical affine coordinates for every distinct Vesta point used by this fixture. -/\n");
        out.push_str(&format!(
            "def capturedPointCoordinates : List (Fq × Fq) := [{}]\n\n",
            point_coordinates.join(", ")
        ));
        out.push_str("def capturedPointCoordinatesValid : Bool :=\n");
        out.push_str(
            "  capturedPointCoordinates.all fun p => decide (OnCurve Vesta.a Vesta.b p) || decide (p = (0, 0))\n\n",
        );
        out.push_str("theorem capturedPointCoordinatesValid_eq_true : capturedPointCoordinatesValid = true := by native_decide\n\n");
        out.push_str("def mkVestaPoint (p : Fq × Fq) : G :=\n");
        out.push_str("  if h : OnCurve Vesta.a Vesta.b p then ⟨p.1, p.2, Or.inl h⟩\n");
        out.push_str("  else if h0 : p = (0, 0) then ⟨p.1, p.2, Or.inr h0⟩ else 0\n\n");
        out.push_str(
            "def capturedPoints : List G := capturedPointCoordinates.map mkVestaPoint\n\n",
        );
        out.push_str("def capturedPoint (i : ℕ) : G := capturedPoints.getD i 0\n\n");
        out.push_str(&body);
        out
    }
}

#[cfg(test)]
mod tests {
    use group::prime::PrimeCurveAffine;

    use super::*;

    #[test]
    fn transcript_schedule_records_squeeze_before_first_proof_read() {
        let vk_repr = Fp::from(1);
        let theta = Fp::from(2);
        let beta = Fp::from(3);
        let events = [
            TranscriptEvent::CommonScalar(vk_repr),
            // A zero-advice circuit squeezes theta without first reading an advice commitment.
            TranscriptEvent::Squeeze(theta),
            TranscriptEvent::ReadPoint(EqAffine::generator()),
            TranscriptEvent::Squeeze(beta),
        ];
        let mut points = PointTable::new();

        let (captured_init, schedule_entries) = render_transcript_capture(&mut points, &events, 1);

        assert_eq!(captured_init, vec![transcript_scalar(vk_repr)]);
        assert_eq!(schedule_entries.len(), 2);
        assert!(schedule_entries[0].ends_with(&format!(", {})", fp(theta))));
        assert!(schedule_entries[1].ends_with(&format!(", {})", fp(beta))));
    }

    #[test]
    fn lean_identifier_grammar() {
        // Accepted: letter/underscore start, ASCII alphanumerics and `_` thereafter.
        assert!(is_lean_ident("Halo2"));
        assert!(is_lean_ident("_private"));
        assert!(is_lean_ident("Fixture0"));
        // Rejected: empty, digit-leading (the case release builds previously waved through), and
        // any non-`_` punctuation (a dotted path is validated segment-by-segment by the caller).
        assert!(!is_lean_ident(""));
        assert!(!is_lean_ident("123"));
        assert!(!is_lean_ident("0abc"));
        assert!(!is_lean_ident("has-hyphen"));
        assert!(!is_lean_ident("has.dot"));
        assert!(!is_lean_ident("has space"));
    }
}
