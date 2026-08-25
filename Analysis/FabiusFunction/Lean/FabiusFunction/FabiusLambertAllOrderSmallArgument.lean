import FabiusFunction.FabiusLambertAllOrderRemainder
import FabiusFunction.FabiusLambertRates

/-!
# Literal small-argument lower-Lambert expansion

The all-order dyadic-coordinate expansion is transported to `x → 0⁺`.
Besides the exact inverse-logarithmic form, this module exposes a version
written solely in terms of `-log x`, `log (-log x)`, and the recursive
coefficient polynomials.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter Asymptotics Set Finset

namespace Fabius

/-- The arbitrary-order lower-Lambert approximation expressed through the
inverse dyadic logarithmic coordinate. -/
noncomputable def fabiusLambertLogarithmicApproximation
    (N : ℕ) (x : ℝ) : ℝ :=
  fabiusSmallArgumentLog x +
    ∑ n ∈ Finset.range (N + 1),
      dyadicLambertDisplacementCoefficient n
        (Real.log (fabiusSmallArgumentLog x)) /
          (fabiusSmallArgumentLog x) ^ n

/-- Transport along `t ↦ 2 ^ (-t)`: the order-`N` logarithmic-coordinate
approximation evaluated at `fabiusLogArgument t` equals the dyadic-coordinate
approximation at `t`, for every real `t`.  Used in this file by
`fabiusLambertPhase_sub_logarithmicApproximation_isBigO`. -/
theorem fabiusLambertLogarithmicApproximation_dyadic
    (N : ℕ) (t : ℝ) :
    fabiusLambertLogarithmicApproximation N (fabiusLogArgument t) =
      dyadicLambertPhaseApproximation N t := by
  rw [fabiusLambertLogarithmicApproximation,
    fabiusSmallArgumentLog_logArgument,
    dyadicLambertPhaseApproximation]

/-- The exact Lambert phase has the recursive expansion of every order at
small positive arguments, in the inverse-logarithmic coordinate. -/
theorem fabiusLambertPhase_sub_logarithmicApproximation_isBigO (N : ℕ) :
    (fun x : ℝ => fabiusLambertPhase x -
      fabiusLambertLogarithmicApproximation N x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹ ^ N) := by
  apply isBigO_smallArgument_of_logScale
  have h := dyadicLambertAllOrderRemainder_isBigO N
  apply h.congr'
  · filter_upwards with t
    unfold dyadicLambertAllOrderRemainder
    have ha := fabiusLambertLogarithmicApproximation_dyadic N t
    unfold fabiusLogArgument at ha ⊢
    rw [fabiusLambertPhase_dyadic, ha]
  · filter_upwards with t
    rw [fabiusSmallArgumentLog_logArgument]

/-- Literal all-order approximation in the source variables `-log x` and
`log (-log x)`. -/
noncomputable def fabiusLambertLiteralApproximation
    (N : ℕ) (x : ℝ) : ℝ :=
  -Real.log x / Real.log 2 +
    ∑ n ∈ Finset.range (N + 1),
      dyadicLambertDisplacementCoefficient n
        (Real.log (-Real.log x) - Real.log (Real.log 2)) *
          (Real.log 2 / (-Real.log x)) ^ n

private theorem logarithmicApproximation_eq_literal
    (N : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    fabiusLambertLogarithmicApproximation N x =
      fabiusLambertLiteralApproximation N x := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmx : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hx hx1)
  have ht : fabiusSmallArgumentLog x =
      (-Real.log x) / Real.log 2 := by
    unfold fabiusSmallArgumentLog Real.logb
    ring
  have hlogq : Real.log ((-Real.log x) / Real.log 2) =
      Real.log (-Real.log x) - Real.log (Real.log 2) := by
    rw [Real.log_div hmx.ne' hL.ne']
  unfold fabiusLambertLogarithmicApproximation
  unfold fabiusLambertLiteralApproximation
  rw [ht, hlogq]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [div_eq_mul_inv, ← inv_pow]
  congr 1
  field_simp [hmx.ne', hL.ne']

private theorem eventually_logarithmicApproximation_eq_literal (N : ℕ) :
    fabiusLambertLogarithmicApproximation N =ᶠ[nhdsWithin 0 (Ioi 0)]
      fabiusLambertLiteralApproximation N := by
  have hxlt : Iio (1 : ℝ) ∈ nhdsWithin 0 (Ioi 0) :=
    Filter.mem_of_superset
      (Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))))
      (by intro x hx; exact hx.2)
  filter_upwards [self_mem_nhdsWithin, hxlt] with x hx hx1
  exact logarithmicApproximation_eq_literal N hx hx1

private theorem smallArgumentLog_inv_pow_isBigO_literal (N : ℕ) :
    (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹ ^ N)
      =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => ((-Real.log x)⁻¹) ^ N) := by
  have h := (isBigO_refl
    (fun x : ℝ => ((-Real.log x)⁻¹) ^ N)
      (nhdsWithin 0 (Ioi 0))).const_mul_left ((Real.log 2) ^ N)
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [smallArgumentLog_inv_eq hx, mul_pow]

/-- Literal all-order lower-Lambert expansion at `x → 0⁺`.  The
coefficient functions contain only `log x`, `log (-log x)`, and the explicit
recursive displacement polynomials. -/
theorem fabiusLambertPhase_sub_literalApproximation_isBigO (N : ℕ) :
    (fun x : ℝ => fabiusLambertPhase x -
      fabiusLambertLiteralApproximation N x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => ((-Real.log x)⁻¹) ^ N) := by
  have h := (fabiusLambertPhase_sub_logarithmicApproximation_isBigO N).trans
    (smallArgumentLog_inv_pow_isBigO_literal N)
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_logarithmicApproximation_eq_literal N] with x hx
  rw [hx]

end Fabius
