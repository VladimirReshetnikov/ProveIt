# Additional local simplification: integer nonzero certificates

## Source and novelty boundary

Pinned repository commit: `7df43cdfacb490cd3ca3acd23e39027efebf8801`.

Target: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticNonzero.lean`, definition `DiophantineConsistency.Rep.nonzero`, correctness field at lines 20–35 (arithmetic block at lines 24–35).

Permanent source: https://github.com/VladimirReshetnikov/ProveIt/blob/7df43cdfacb490cd3ca3acd23e39027efebf8801/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticNonzero.lean

The exclusion audit searched all 23 placed packets and five incoming archives. No proposal specifically addressing `ArithmeticNonzero`, `Rep.nonzero`, or the square-minus-one nonzero certificate was found. This is a modest additional local use of integer discreteness and square positivity. It is not a new Diophantine representation, a new canonical-witness framework, or a new general mechanism for eliminating existential variables. Those broader directions are prior work.

## Exact idea

After the existing expression-evaluation normalization, the correctness goal is

    z ≠ 0 ↔ ∃ w : Fin 1 → ℕ, z*z - 1 - (w 0 : ℤ) = 0.

The current proof separates negative and positive integers, invokes `nlinarith` on both sign branches, chooses `(z*z-1).toNat`, rewrites its cast, and closes the equality by `ring`.

Use the existing ordered-ring theorem `mul_self_pos` to state precisely the needed fact:

    0 < z*z ↔ z ≠ 0.

For integers, positivity is equivalent to being at least one. Thus

    z ≠ 0  →  0 < z*z  →  1 ≤ z*z  →  0 ≤ z*z-1.

`Int.eq_ofNat_of_zero_le` then supplies a natural number whose cast is exactly `z*z-1`. The witness function is constant at that natural number. In the other direction, the certificate equation and nonnegativity of the natural slack imply `0 < z*z`; `mul_self_pos.mp` finishes. The only remaining `omega` call sees `z*z` as one atom and solves a linear integer inequality.

The proof does not depend on the sign of the expression and retains negative inputs, zero rejection, and both unit cases.

## Exact replacement

```lean
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le
        (Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr (mul_self_pos.mpr hz)))
      exact ⟨fun _ => n, sub_eq_zero.mpr hn⟩
    · rintro ⟨w, hw⟩
      apply mul_self_pos.mp
      have := Int.natCast_nonneg (w 0)
      omega
```

There is no production helper and no change to imports or public signatures. The `witnessCount` field remains literally `1`; the polynomial expression field is byte-for-byte unchanged. Only the correctness proof changes.

## Measured scope

- Exact source patch: `semantic_arithmetic_nonzero.patch`.
- Full candidate module: `semantic_ArithmeticNonzero.lean`.
- Source metrics: 68 physical module lines become 65; arithmetic proof block 12 becomes 9. Net reduction: **3 physical lines**. Do not inflate this into a broad reduction or performance result.
- Standalone comparison: `semantic_nonzero.lean` contains the original arithmetic proof and the replacement at the exact generalized goal.
- Lean version: 4.32.0.
- Mathlib version: `81a5d257c8e410db227a6665ed08f64fea08e997` (shared pinned checkout prepared by root).
- Both standalone proofs compiled successfully. Both report the same axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `git apply --check` succeeded at the pinned source tree.
- The full production dependency closure was **not** rebuilt for this candidate. Therefore the checked claim is the exact arithmetic replacement after the unchanged normalization, plus textual patch applicability. Whole-module and downstream integration checks remain an integration step.
- No timing improvement is claimed. The simplification removes local sign splitting, two nonlinear tactic branches, a cast rewrite, and ring normalization; source savings are deliberately described as small.

## Reproduction

In a Lean 4.32.0 project with the pinned mathlib dependency:

    lake env lean semantic_nonzero.lean

For integration, from the pinned ProveIt repository root:

    git apply --check semantic_arithmetic_nonzero.patch
    git apply semantic_arithmetic_nonzero.patch

Then rebuild the existing `DiophantineConsistency.ArithmeticNonzero` target and its relevant clients through the repository's normal build entry point. No repository mutation was performed during this review.

## Rejected nearby ideas

1. `AnnotatedSchema.exists_separation_program_iff` and `AnnotatedReplacement.exists_program_iff` can be shortened by determined existential witness elimination. Packet s already proposes that mechanism, including `exists_and_left` and `exists_eq_left`; omitted as a repeated idea.
2. `ExecutableJones.fromRep_correct` can reuse `eval_fromRep_polynomial` and the compiler result's correctness projection. Generic endpoint relation transport is already prior; omitted as a headline.
3. Internal-natural Boolean idempotence via multiplicative cancellation, and moving the strict ordered-semiring instance before discreteness, are explicitly present in a current incoming archive; omitted.
4. Specialized iterator/fold congruence, constructor views, schema index-map normalization, scalar PR composition automation, witness-layout transport, and finite residual normalization are all assumed applied.
