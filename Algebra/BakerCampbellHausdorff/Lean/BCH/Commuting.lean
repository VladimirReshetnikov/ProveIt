/-
# The commuting case of the Baker–Campbell–Hausdorff formula

This file formalizes Proposition 9.1 of the accompanying article
(`docs/combined`, Section 9.1): if `[X, Y] = 0` in a real or complex
unital Banach algebra, then `e^X e^Y = e^{X+Y}`, without any smallness
hypothesis.

## Setting

Throughout the Lean development, "a real or complex unital Banach algebra
with a submultiplicative norm" is rendered as

* `[RCLike 𝕂]` — the scalar field is `ℝ` or `ℂ`;
* `[NormedRing 𝔸]` — a unital ring with a submultiplicative norm
  (`‖a * b‖ ≤ ‖a‖ * ‖b‖`); no normalization `‖1‖ = 1` is assumed, in
  agreement with Section 7.1 of the article;
* `[NormedAlgebra 𝕂 𝔸]` — the scalar action is compatible with the norm;
* `[CompleteSpace 𝔸]` — completeness.

The bracket `⁅X, Y⁆` is the ring commutator `X * Y - Y * X`
(`Ring.lie_def`), exactly the convention `[A, B] = AB - BA` of Section 1.3.
The exponential is Mathlib's `NormedSpace.exp`, the sum of the series
`∑ Xⁿ/n!`. Mathlib defines it through the (unique) `ℚ`-algebra structure of
`𝔸`; inside proofs that structure is supplied by restriction of scalars from
`𝕂`, following Mathlib's own usage.
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Algebra.Lie.OfAssociative

open NormedSpace

namespace BCH

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

include 𝕂

/-- **Proposition 9.1 (commuting case).** If `[X, Y] = 0`, then
`e^X e^Y = e^{X + Y}` for all `X, Y` in a real or complex unital Banach
algebra, without a smallness hypothesis. The scalar field `𝕂` is an
explicit argument because it does not occur in the statement. -/
theorem exp_mul_exp_of_lie_eq_zero {X Y : 𝔸} (h : ⁅X, Y⁆ = 0) :
    exp X * exp Y = exp (X + Y) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hc : Commute X Y := by
    rw [Ring.lie_def, sub_eq_zero] at h
    exact h
  exact (exp_add_of_commute hc).symm

end BCH
