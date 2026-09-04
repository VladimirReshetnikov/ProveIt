import FabiusFunction.EulerPolynomials

/-!
# The reflection formula for Euler polynomials

`E_n(1 - x) = (-1)^n E_n(x)`, hence `E_{2m+1}(1/2) = 0`.

Replacing `x` by `1 - x` in `E(x,t) (e^t + 1) = 2 e^{xt}` gives
`E(1-x,t) (e^t + 1) = 2 e^t e^{-xt}`, and replacing `t` by `-t` gives
`E(x,-t) (e^{-t} + 1) = 2 e^{-xt}`, i.e. `E(x,-t) (e^t + 1) = 2 e^t e^{-xt}` as well;
cancelling the unit `e^t + 1` identifies the two series coefficientwise.

## Main results

* `eulerPolynomial_comp_one_sub`: `E_n(1 - X) = (-1)^n E_n` in `ℚ[X]`.
* `eulerPolynomial_eval_one_sub`: the reflection formula.
* `eulerPolynomial_eval_half_odd`: `E_{2m+1}(1/2) = 0`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- `rescale a (e^t) = e^{at}` over any `ℚ`-algebra. -/
theorem rescale_exp_eq_expSeries' (A : Type*) [CommRing A] [Algebra ℚ A] (a : A) :
    PowerSeries.rescale a (PowerSeries.exp A) = expSeries A a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, expSeries, coeff_egfA, mul_comm]

/-- `rescale (-1)` of the Euler generating function. -/
theorem rescale_neg_one_egfA_eulerPolynomial :
    PowerSeries.rescale (-1 : ℚ[X]) (egfA ℚ[X] eulerPolynomial) =
      egfA ℚ[X] (fun n => (-1) ^ n * eulerPolynomial n) := by
  ext n
  rw [PowerSeries.coeff_rescale, coeff_egfA, coeff_egfA]
  ring

/-- `rescale (-1)` of `e^{xt}` is `e^{-xt}`. -/
theorem rescale_neg_one_expSeries_X :
    PowerSeries.rescale (-1 : ℚ[X]) (expSeries ℚ[X] X) = expSeries ℚ[X] (-X) := by
  ext n
  rw [PowerSeries.coeff_rescale, expSeries, expSeries, coeff_egfA, coeff_egfA, neg_pow]
  ring

/-- Substituting `1 - x` into the Euler generating function. -/
theorem map_compRingHom_egfA_eulerPolynomial :
    PowerSeries.map (compRingHom (1 - X : ℚ[X])) (egfA ℚ[X] eulerPolynomial) =
      egfA ℚ[X] (fun n => (eulerPolynomial n).comp (1 - X)) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_egfA, coeff_egfA, coe_compRingHom_apply, mul_comp,
    Polynomial.algebraMap_eq, C_comp]

/-- Substituting `1 - x` into `e^{xt}`. -/
theorem map_compRingHom_expSeries_X :
    PowerSeries.map (compRingHom (1 - X : ℚ[X])) (expSeries ℚ[X] X) = expSeries ℚ[X] (1 - X) := by
  ext n
  rw [PowerSeries.coeff_map, expSeries, expSeries, coeff_egfA, coeff_egfA, coe_compRingHom_apply,
    mul_comp, Polynomial.algebraMap_eq, C_comp, pow_comp, X_comp]

/-- **Reflection, polynomial form:** `E_n(1 - X) = (-1)^n E_n`. -/
theorem eulerPolynomial_comp_one_sub (n : ℕ) :
    (eulerPolynomial n).comp (1 - X) = (-1) ^ n * eulerPolynomial n := by
  -- the generating function identity `E(x,t) (e^t + 1) = 2 e^{xt}`
  have hgf : egfA ℚ[X] eulerPolynomial * (PowerSeries.exp ℚ[X] + 1) = 2 * expSeries ℚ[X] X := by
    rw [egfA_eulerPolynomial, mul_right_comm, egfA_C_eulerNumberZero_mul]
  -- substitute `x ↦ 1 - x`
  have h1 : egfA ℚ[X] (fun n => (eulerPolynomial n).comp (1 - X)) * (PowerSeries.exp ℚ[X] + 1)
      = 2 * expSeries ℚ[X] (1 - X) := by
    have h := congrArg (PowerSeries.map (compRingHom (1 - X : ℚ[X]))) hgf
    rwa [map_mul, map_add, PowerSeries.map_exp, map_one, map_mul, map_ofNat,
      map_compRingHom_egfA_eulerPolynomial, map_compRingHom_expSeries_X] at h
  -- substitute `t ↦ -t`
  have h2 : egfA ℚ[X] (fun n => (-1) ^ n * eulerPolynomial n) * (PowerSeries.exp ℚ[X] + 1)
      = 2 * expSeries ℚ[X] (1 - X) := by
    have h := congrArg (PowerSeries.rescale (-1 : ℚ[X])) hgf
    rw [map_mul, map_add, map_one, map_mul, map_ofNat, rescale_neg_one_egfA_eulerPolynomial,
      rescale_neg_one_expSeries_X, rescale_exp_eq_expSeries'] at h
    -- multiply through by `e^t = expSeries 1`
    have hmul : egfA ℚ[X] (fun n => (-1) ^ n * eulerPolynomial n) * (expSeries ℚ[X] (-1) + 1) *
        expSeries ℚ[X] 1 = 2 * expSeries ℚ[X] (-X) * expSeries ℚ[X] 1 := by
      rw [h]
    have he : expSeries ℚ[X] (-1) * expSeries ℚ[X] 1 = 1 := by
      rw [expSeries_mul, show (-1 : ℚ[X]) + 1 = 0 by ring, expSeries_zero]
    have hexp1 : PowerSeries.exp ℚ[X] = expSeries ℚ[X] 1 := exp_eq_expSeries_one ℚ[X]
    rw [hexp1]
    calc egfA ℚ[X] (fun n => (-1) ^ n * eulerPolynomial n) * (expSeries ℚ[X] 1 + 1)
        = egfA ℚ[X] (fun n => (-1) ^ n * eulerPolynomial n) * (expSeries ℚ[X] (-1) + 1) *
            expSeries ℚ[X] 1 := by
          linear_combination (-(egfA ℚ[X] fun n => (-1) ^ n * eulerPolynomial n)) * he
      _ = 2 * expSeries ℚ[X] (-X) * expSeries ℚ[X] 1 := by rw [hmul]
      _ = 2 * expSeries ℚ[X] (1 - X) := by
          rw [mul_assoc, expSeries_mul]
          congr 2
          ring
  -- cancel the unit `e^t + 1`
  have hunit : IsUnit (PowerSeries.exp ℚ[X] + 1) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, PowerSeries.constantCoeff_exp, map_one,
      one_add_one_eq_two, ← map_ofNat (C : ℚ →+* ℚ[X]) 2]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr two_ne_zero)
  have h3 : egfA ℚ[X] (fun n => (eulerPolynomial n).comp (1 - X))
      = egfA ℚ[X] (fun n => (-1) ^ n * eulerPolynomial n) :=
    hunit.mul_right_cancel (h1.trans h2.symm)
  have hc := congrArg (PowerSeries.coeff n) h3
  rw [coeff_egfA, coeff_egfA, Polynomial.algebraMap_eq] at hc
  have hC : (C (1 / (n.factorial : ℚ)) : ℚ[X]) ≠ 0 := by
    rw [ne_eq, C_eq_zero]
    exact one_div_ne_zero (by positivity)
  exact mul_left_cancel₀ hC hc

/-- **The reflection formula:** `E_n(1 - x) = (-1)^n E_n(x)`. -/
theorem eulerPolynomial_eval_one_sub (n : ℕ) (x : ℚ) :
    (eulerPolynomial n).eval (1 - x) = (-1) ^ n * (eulerPolynomial n).eval x := by
  have h := congrArg (Polynomial.eval x) (eulerPolynomial_comp_one_sub n)
  rw [eval_comp, eval_sub, eval_one, eval_X, eval_mul, eval_pow, eval_neg, eval_one] at h
  exact h

/-- `E_{2m+1}(1/2) = 0`. -/
theorem eulerPolynomial_eval_half_odd (m : ℕ) :
    (eulerPolynomial (2 * m + 1)).eval (1 / 2 : ℚ) = 0 := by
  have h := eulerPolynomial_eval_one_sub (2 * m + 1) (1 / 2)
  rw [show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num, pow_succ, pow_mul] at h
  norm_num at h
  linarith

end Fabius
