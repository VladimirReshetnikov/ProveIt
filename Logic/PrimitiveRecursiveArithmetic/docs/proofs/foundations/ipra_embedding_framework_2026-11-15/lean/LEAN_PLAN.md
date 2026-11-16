# Lean completion plan

## Status

`FiniteTraceSemantic.lean` is an ordinary Lean prototype. It is not an iPRA
formalization. `IPRAObjectLanguageBlueprint.lean` identifies the exact
object-language endpoint and intentionally leaves the nontrivial embedded
proofs to be constructed in the ProveIt workspace. Lean/Lake was unavailable
in the artifact-building environment, so neither file was compiled here.

## Existing ProveIt interfaces to reuse

1. `ConciseIPRA.PR`: `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, and the defining
   equations for composition and primitive recursion.
2. `ConciseIPRA.Deduction`: intuitionistic formulas and derivations.
3. `ConciseIPRA.Native`: `NFm`, `NPrf`, substitution, and native soundness.
4. `ConciseIPRA.NativeBiInterpretation`: `pra_iff_native` and
   `native_iff_pra`.
5. `ConciseIPRA.NativePublic`: guarded public formulas and a
   substitution-stable certificate language when compact external
   certificates are desired.

## Dependency-ordered implementation

1. **Codes.** Select one canonical code for Booleans, pairs, lists, signed
   integers, and positive-denominator rationals. Avoid parallel encodings.
2. **Boolean folds.** Implement bounded `all`, `any`, sum, product, maximum,
   and first-witness search. Prove accumulator invariants with `PRA.qfInd`.
3. **Trace reflection.** Implement the formulas described in
   `IPRAObjectLanguageBlueprint.lean`; prove base, step, and final composition.
4. **Finite query tables.** A trace declares every input-name precision it
   reads. Build a primitive-recursive table and a Boolean `GoodTable`; derive
   it by finitely instantiating global regularity/domain hypotheses.
5. **Rational kernel.** Prove cross-multiplication correctness, denominator
   positivity, absolute value, and interval arithmetic.
6. **Precision algebra.** Implement monotone precision transformers and the
   operation contracts for sums, products, reciprocals under apartness,
   finite products, and polynomial evaluation.
7. **Robust control.** Formalize the overlapping-branch and exact-gap lemmas.
   Every division/pivot/chart theorem should consume an explicit domain or
   apartness certificate.
8. **Finite nets.** Implement grid generation, bounded minimization, and the
   Lipschitz transfer theorem. Exact objects arise from coherent nested
   certificates, not from an unqualified choice of a point in every net.
9. **Domain packages.** Layer polynomial, matrix, analytic, probability, and
   Diophantine libraries on the shared kernel.
10. **Native export.** Close the intended `[] ⊢[PRAAx] phi` theorem and apply
    `pra_iff_native`. Audit all endpoint declarations with `#print axioms` and
    scan for `sorry`, `admit`, and new `axiom` declarations.

## Main theorem targets

- `PRA.traceReflection`
- `PRA.booleanFoldAll_correct`
- `PRA.fixedPrecision_then_all`
- `PRA.regularName_add`, `mul`, `inv_of_apart`
- `PRA.overlappingBranch`, `exactBranch_of_gap`
- `PRA.finiteNet_minResidual`
- `PRA.nestedBalls_regularName`
- `PRA.heightBound_completeList`
- `PRA.completeList_heightBound`
- `PRA.certificateVerifier_sound`

Each theorem should be an embedded derivation, not merely an ambient Lean
proposition.
