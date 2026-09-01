import FabiusFunction.QPochhammerComplexOrder
import FabiusFunction.QPochhammerLogDerivative
import FabiusFunction.QBinomialTheoremInfinite

/-!
# The derivative of a q-Pochhammer symbol with respect to its order

With `q^α = exp(α log q)`, the symbol `(a;q)_α = (a;q)_∞/(aq^α;q)_∞` is
differentiable in `α` wherever `‖aq^α‖ < 1`, and its logarithmic derivative is

`∂_α (a;q)_α / (a;q)_α = (log q) ∑_{j≥0} aq^{α+j}/(1 - aq^{α+j})`.

This is the chain rule applied to the derivative of `x ↦ (x;q)_∞`
(`QPochhammerLogDerivative`) along `α ↦ aq^α`, whose derivative is
`aq^α log q`.

## Main declarations

* `hasDerivAt_const_cpow'`: `∂_α q^α = q^α log q`.
* `hasDerivAt_qPochhammerInfIn_mul_cpow`: `∂_α (aq^α;q)_∞`.
* `hasDerivAt_qPochhammerC`: `∂_α (a;q)_α` in logarithmic form.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-- `∂_α q^α = q^α log q` for `q ≠ 0`. -/
theorem hasDerivAt_const_cpow' {q : ℂ} (hq0 : q ≠ 0) (α : ℂ) :
    HasDerivAt (fun β : ℂ => q ^ β) (q ^ α * Complex.log q) α :=
  (Complex.hasStrictDerivAt_const_cpow (Or.inl hq0)).hasDerivAt

/-- `∂_α (aq^α;q)_∞ = -(aq^α;q)_∞ (∑_j q^j/(1 - aq^α q^j)) · aq^α log q` for `‖aq^α‖ < 1`. -/
theorem hasDerivAt_qPochhammerInfIn_mul_cpow {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {a α : ℂ}
    (h : ‖a * q ^ α‖ < 1) :
    HasDerivAt (fun β : ℂ => qPochhammerInfIn (a * q ^ β) q)
      (-(qPochhammerInfIn (a * q ^ α) q * ∑' j : ℕ, q ^ j / (1 - a * q ^ α * q ^ j)) *
        (a * (q ^ α * Complex.log q))) α := by
  have h1 := hasDerivAt_qPochhammerInfIn hq h
  have h2 := (hasDerivAt_const_cpow' hq0 α).const_mul a
  exact h1.comp α h2

/-- **The derivative with respect to the order**: for `‖q‖ < 1`, `q ≠ 0`, and
`‖aq^α‖ < 1`,
`∂_α (a;q)_α = (a;q)_α · (log q) ∑_{j≥0} aq^{α+j}/(1 - aq^{α+j})`. -/
theorem hasDerivAt_qPochhammerC {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {a α : ℂ}
    (h : ‖a * q ^ α‖ < 1) :
    HasDerivAt (fun β : ℂ => qPochhammerC a q β)
      (qPochhammerC a q α *
        (Complex.log q * ∑' j : ℕ, a * q ^ (α + j) / (1 - a * q ^ (α + j)))) α := by
  have hP : qPochhammerInfIn (a * q ^ α) q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq h
  have hfun : (fun β : ℂ => qPochhammerC a q β) =
      fun β : ℂ => qPochhammerInfIn a q * (qPochhammerInfIn (a * q ^ β) q)⁻¹ :=
    funext fun β => div_eq_mul_inv _ _
  rw [hfun]
  refine ((hasDerivAt_qPochhammerInfIn_mul_cpow hq hq0 h).inv hP).const_mul
    (qPochhammerInfIn a q) |>.congr_deriv ?_
  have hsum : ∑' j : ℕ, a * q ^ (α + j) / (1 - a * q ^ (α + j)) =
      a * q ^ α * ∑' j : ℕ, q ^ j / (1 - a * q ^ α * q ^ j) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [Complex.cpow_add _ _ hq0, Complex.cpow_natCast, ← mul_assoc, mul_div_assoc]
  rw [hsum, qPochhammerC, neg_mul, neg_neg, pow_two,
    mul_assoc (qPochhammerInfIn (a * q ^ α) q), mul_div_mul_left _ _ hP]
  ring

end Fabius
