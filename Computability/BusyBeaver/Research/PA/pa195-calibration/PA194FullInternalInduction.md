# Arbitrary internal PA induction axioms

`PA194FullInternalInduction.internal_induction_body` proves the following model-uniform statement: in every arithmetic model of IΣ₁, for every code `K` satisfying `IsSemiformula ℒₒᵣ 1 K`, the Foundation internal PA provability predicate holds of `indBodyVal K`. The formula code may be nonstandard.

The construction binds every free label to a bound slot, proves the resulting body is well formed and shift-fixed, chooses its actual `bv` as the model-length closure, and proves that substitution by `fvarVec` recovers the original formula. It then constructs the exact `InductionUnivR` witness and opens all quantifiers in a model-length internal PA proof. `PA194BindAllDecode.bindAll_decode` establishes the general formula-level inverse under a vector invariant; `bindAll_root_inverse` specializes it with no extra free-label-bound hypothesis.

This is a model-uniform internal PA provability theorem. It does not itself construct a fixed finite proof-transformer code, prove internal bounded comprehension or the distinct-label gate, establish an iPRA derivation, or prove the PA194 machine consistency equivalence.

The author replay ran `check-full-internal-induction.sh` against the pinned Foundation overlay, rebuilding all seventeen local modules. The reported axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
