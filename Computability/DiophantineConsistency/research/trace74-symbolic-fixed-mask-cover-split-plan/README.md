# Proposed non-expanding symbolic mask-cover split

This is a source-only contingency plan, not a Lean result. The original single-stage check was deliberately terminated under its pinned runner; its retained result records no accepted theorem. The separately copied [v2 draft](../trace74-symbolic-fixed-mask-cover-draft-v2/Trace74SymbolicFixedMaskCover.lean) preserves the strict chain `defect < B^3297 <= B^4393 <= highNat` and finishes with successor monotonicity. The original v1 `cover_nat` retained only `defect <= highNat`, which alone is insufficient because the low identity contains an additional `+1`. No live pinned input has been changed.

If splitting is needed, prepare separately reviewed and bounded stages on the same selected symbolic providers:

1. **Short support and defect.** Prove `support subset range 3297`; truncate the 8807-term defect sum; package the 3297-digit list, the existing `digits_add_defect` identity and `Nat.ofDigits_lt_base_pow_length` as `lowNat+defect+1=B^8807` and `defect<B^3297`. Preserve the exact symbolic low port.
2. **High digit bound.** Separate the high-digit prefix/suffix list equality and prefix length from the generic `Nat.ofDigits_append` lower-bound lemma. The intended `mu` digit occurs at index 4393; prove its positivity without evaluating the full high mask. If a list simplification is expensive, preserve named prefix/suffix definitions as opaque after their source-level identities have been established.
3. **Abstract cover arithmetic.** For abstract natural `low,defect,high,beta,power`, prove that `beta+1=low+defect+1` and `defect<high` imply `beta+1<=low+high`, using successor and addition monotonicity. Apply it only after the two bound stages. Avoid `omega` on the concrete large mask definitions.
4. **Model cast.** Cast the completed natural inequality into an arbitrary IΣ₁ model using the existing standard cast-order theorem. Record its own axiom report and selected symbolic provider identities.

Each stage must have pinned sources/imports and an independently reviewed guarded runner before Lean. No empirical timing locates the expense within the original single stage yet: plausible candidates are long high-list append normalization and simplifier/definitional unfolding around concrete `Nat.ofDigits` and powers. No claim of a fixed-port guard, no-carry necessity or graph theorem follows from a mask-cover inequality alone.

The [independent factual/source audit](../../reviews/trace74-symbolic-mask-stop-v2-independent/README.md) checked the controlled-stop evidence and strict v2 correction. This plan itself does not certify any proposed stage.
