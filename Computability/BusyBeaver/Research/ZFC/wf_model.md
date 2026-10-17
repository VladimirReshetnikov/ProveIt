# A direct well-founded model for the machine's native theory

The new Lean comparison is

```lean
WFTheory.c254_refutation_iff_zf :
  Code254.C254 Code254.F ↔ BProv SetTheory.ZFax_s [] Form.fBot
```

`ZFax_s` includes Power Set and Foundation. Consequently the machine's exact
numerical calculus and `NativeAx` are equiconsistent with ordinary ZF.
This is an external Lean theorem; Choice removal and the requested internal PA
proof still require their own constructions. The binary endpoint also waits
for the complete finite site certificate.

## Why the direct route is shorter

The quotient already supplies more than the six-field `ZFAxioms` bundle:
its Global-Image Collection schema proves that a set all of whose members are
internally well-founded is itself internally well-founded.
`WellFoundedPart.quotient_wf_closure` derives this from one actual formula
instance collecting well-founded witnesses. We can use that resource directly
instead of first proving a general Foundation-removal theorem for arbitrary
models of ZF without Foundation. The general theorem remains a separate target.

`WFModel` constructs the internally well-founded subtype with inherited
membership. It assumes the ambient six-field bundle, exact powersets and the
stated closure property; it never assumes ambient Foundation or external
well-foundedness of the membership relation. The earlier internal-witness
argument supplies Regularity on the subtype.

The remaining axiom checks are concrete:

- Pairing and Union have only well-founded members, so closure puts their
  witnesses in the subtype.
- Separation uses the actual `WFRelativization.translate` formula and a lifted
  valuation. No arbitrary external-predicate Separation is assumed.
- Replacement uses the translated matrix guarded at both output slot0 and
  input slot1. These guards make the ambient relation globally partial
  functional, including outside the input set. The image has well-founded
  members and hence belongs to the subtype.
- Every subset of a well-founded set has well-founded members. Applying closure
  twice puts the ambient powerset and all its members in the subtype, giving
  the exact internal Power Set axiom.
- Separating the actual well-foundedness formula out of an ambient inductive
  set gives a well-founded inductive set. Empty-set and successor closure are
  established before sealing the ordinary Infinity sentence.

`WFTheory.zf_consistent_of_model` supplies an explicit inhabitant and constant
valuation, then applies soundness to this actual ZF model. Numerical completeness
turns any ZF refutation into `C254 F`. The converse uses the independently
checked rank construction in `ZFNative`, which derives the native axioms in
any ordinary ZF model.

## Verification

The three new modules `WFRelativization`, `WFModel`, and `WFTheory` passed a
fresh serial Lean4.32.0 check. Twenty-three axiom reports and six direct callers
also passed, including a ZF-refutation-to-literal-zero-register-halting caller.
Only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`
occur. An independent full source review found no hidden Choice or Foundation
premise, no external well-foundedness substitution and no missing formula guard.

[The scoped record](results/wf-model-theory-verification.json) retains exact
source hashes, commands, outputs and the initial corrected compilation errors.
[The integration record](results/wf-theory-integration-verification.json)
checks all129 imported source identities against successful scoped builds and
freshly builds the130-unit umbrella plus the joint audit. It is not a fresh
full130-module rebuild. The unrelated finite binary coverage batches continue
separately; this result does not upgrade their status.
