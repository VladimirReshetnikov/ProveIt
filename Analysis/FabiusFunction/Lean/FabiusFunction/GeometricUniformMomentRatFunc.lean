import FabiusFunction.GeometricUniformExteriorComplexMomentGerm
import FabiusFunction.QExponential
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The rational geometric-uniform moment coefficient

The inner complex product for `‖q‖ < 1` and the exterior reciprocal germ for
`1 < ‖q‖` have already been shown to produce the same recursive moment
polynomial after finite-q-Pochhammer normalization.  This file packages their
common Taylor coefficient as the single rational function

`a_n(q) = geometricUniformMomentPolynomial n / qFactorial q n`.

The global statement is a denominator-clearing identity in `RatFunc ℚ`.
Specialization uses `RatFunc.eval` only after proving that the polynomial
q-factorial does not vanish.  In particular, no value is assigned at a genuine
pole by totalized division.  At `q = 1` the polynomial q-factorial specializes
to `n!`, so the apparent finite-q-Pochhammer quotient has a removable
specialization even though its unreduced scalar presentation is `0 / 0` for
positive `n`.

## Main declarations

* `geometricUniformMomentRatFunc`: the common rational Taylor coefficient;
* `qFactorial_mul_geometricUniformMomentRatFunc`: its global pole-clearing
  polynomial identity;
* `eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient`:
  safe specialization to the inner product;
* `eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient`:
  safe specialization to the exterior germ;
* `eval_geometricUniformMomentRatFunc_one`: the removable specialization at
  `q = 1`.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

noncomputable section

private theorem eval₂_qFactorial_X_complex (q : ℂ) (n : ℕ) :
    eval₂ (algebraMap ℚ ℂ) q (qFactorial (X : ℚ[X]) n) = qFactorial q n := by
  simp only [qFactorial, qInt, eval₂_finsetProd, eval₂_finsetSum, eval₂_X_pow]

private theorem qFactorial_X_ne_zero (n : ℕ) :
    qFactorial (X : ℚ[X]) n ≠ 0 := by
  intro hzero
  have h := eval₂_qFactorial_X_complex 0 n
  rw [hzero, eval₂_zero] at h
  simp [qFactorial, qInt] at h

/-- The rational coefficient shared by the inner complex moment product and
the exterior reciprocal moment germ.

Its displayed denominator is the polynomial q-factorial
`[n]_X! = ∏_{j=1}^n (1 + X + ⋯ + X^{j-1})`. -/
noncomputable def geometricUniformMomentRatFunc (n : ℕ) : RatFunc ℚ :=
  RatFunc.mk (geometricUniformMomentPolynomial n) (qFactorial (X : ℚ[X]) n)

/-- Globally in `RatFunc ℚ`, multiplying the common rational coefficient by
the polynomial q-factorial recovers the moment polynomial.  This is the safe
pole-clearing form of the manuscript normalization, including parameters at
which a scalar denominator may vanish. -/
theorem qFactorial_mul_geometricUniformMomentRatFunc (n : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ) (qFactorial (X : ℚ[X]) n) *
        geometricUniformMomentRatFunc n =
      algebraMap ℚ[X] (RatFunc ℚ) (geometricUniformMomentPolynomial n) := by
  rw [geometricUniformMomentRatFunc, RatFunc.mk_eq_div]
  simpa only [mul_comm] using
    (div_mul_cancel₀
      (algebraMap ℚ[X] (RatFunc ℚ) (geometricUniformMomentPolynomial n))
      (RatFunc.algebraMap_ne_zero (qFactorial_X_ne_zero n)))

private theorem eval_geometricUniformMomentRatFunc_of_qFactorial_ne_zero
    {q : ℂ} {n : ℕ} (hq : qFactorial q n ≠ 0) :
    RatFunc.eval (algebraMap ℚ ℂ) q (geometricUniformMomentRatFunc n) =
      eval₂ (algebraMap ℚ ℂ) q (geometricUniformMomentPolynomial n) /
        qFactorial q n := by
  let D : ℚ[X] := qFactorial (X : ℚ[X]) n
  have hD : eval₂ (algebraMap ℚ ℂ) q D ≠ 0 := by
    simpa only [D, eval₂_qFactorial_X_complex] using hq
  have hdiv : RatFunc.denom (geometricUniformMomentRatFunc n) ∣ D := by
    rw [geometricUniformMomentRatFunc, RatFunc.mk_eq_div]
    exact RatFunc.denom_div_dvd _ _
  have hdenom :
      eval₂ (algebraMap ℚ ℂ) q
          (RatFunc.denom (geometricUniformMomentRatFunc n)) ≠ 0 := by
    intro hzero
    exact hD (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (algebraMap ℚ ℂ) q hdiv hzero)
  have hmul := RatFunc.eval_mul
    (f := algebraMap ℚ ℂ) (a := q)
    hdenom
    (show eval₂ (algebraMap ℚ ℂ) q
      (RatFunc.denom
        (algebraMap ℚ[X] (RatFunc ℚ) (qFactorial (X : ℚ[X]) n))) ≠ 0 by simp)
  rw [mul_comm, qFactorial_mul_geometricUniformMomentRatFunc] at hmul
  simp only [RatFunc.eval_algebraMap] at hmul
  change
    eval₂ (algebraMap ℚ ℂ) q (geometricUniformMomentPolynomial n) =
      RatFunc.eval (algebraMap ℚ ℂ) q (geometricUniformMomentRatFunc n) *
        eval₂ (algebraMap ℚ ℂ) q (qFactorial (X : ℚ[X]) n) at hmul
  rw [eval₂_qFactorial_X_complex] at hmul
  exact (eq_div_iff hq).2 hmul.symm

private theorem qFactorial_ne_zero_of_one_lt_norm
    {q : ℂ} (hq : 1 < ‖q‖) (n : ℕ) :
    qFactorial q n ≠ 0 := by
  rw [qFactorial]
  refine prod_ne_zero_iff.mpr fun j hj ↦ ?_
  have hjpos : j + 1 ≠ 0 := by omega
  have hpow : q ^ (j + 1) ≠ 1 := by
    intro h
    have hnorm := congrArg norm h
    rw [norm_pow, norm_one] at hnorm
    exact (one_lt_pow₀ hq hjpos).ne' hnorm
  intro hqInt
  have hzero : 1 - q ^ (j + 1) = 0 := by
    rw [← one_sub_mul_qInt, hqInt, mul_zero]
  exact hpow (sub_eq_zero.mp hzero).symm

/-- For `‖q‖ < 1`, safe evaluation of the common rational function is the
Taylor coefficient of the genuine locally-uniform complex moment product.
The statement includes `q = 0` and every `n`, including `n = 0`. -/
theorem eval_geometricUniformMomentRatFunc_eq_complexMomentProduct_taylorCoefficient
    {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    RatFunc.eval (algebraMap ℚ ℂ) q (geometricUniformMomentRatFunc n) =
      iteratedDeriv n (geometricUniformComplexMomentProduct q) 0 /
        (n.factorial : ℂ) := by
  have hqfac : qFactorial q n ≠ 0 := qFactorial_ne_zero hq n
  rw [eval_geometricUniformMomentRatFunc_of_qFactorial_ne_zero hqfac,
    geometricUniformMomentPolynomial_eval₂_eq_complexMomentProduct_taylorCoefficient hq]
  rw [← qFactorial_mul_one_sub_pow]
  have hq1 : 1 - q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  field_simp [hqfac, hq1]

private theorem qFactorial_one_complex (n : ℕ) :
    qFactorial (1 : ℂ) n = (n.factorial : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qFactorial_succ, ih, qInt_one_left, Nat.factorial_succ]
      push_cast
      ring

/-- For `1 < ‖q‖`, safe evaluation of the same rational function is the
Taylor coefficient of the genuine exterior reciprocal germ. -/
theorem eval_geometricUniformMomentRatFunc_eq_exteriorComplexMomentGerm_taylorCoefficient
    {q : ℂ} (hq : 1 < ‖q‖) (n : ℕ) :
    RatFunc.eval (algebraMap ℚ ℂ) q (geometricUniformMomentRatFunc n) =
      iteratedDeriv n (geometricUniformExteriorComplexMomentGerm q) 0 /
        (n.factorial : ℂ) := by
  have hqfac : qFactorial q n ≠ 0 := qFactorial_ne_zero_of_one_lt_norm hq n
  rw [eval_geometricUniformMomentRatFunc_of_qFactorial_ne_zero hqfac,
    geometricUniformMomentPolynomial_eval₂_eq_exteriorComplexMomentGerm_taylorCoefficient hq]
  rw [← qFactorial_mul_one_sub_pow]
  have hq1 : 1 - q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    subst q
    norm_num at hq
  field_simp [hqfac, hq1]

/-- At `q = 1`, the polynomial q-factorial is `n!`, so the common rational
coefficient has a safe removable specialization rather than the totalized
`0 / 0` obtained from the unreduced finite-q-Pochhammer quotient. -/
theorem eval_geometricUniformMomentRatFunc_one (n : ℕ) :
    RatFunc.eval (algebraMap ℚ ℂ) 1 (geometricUniformMomentRatFunc n) =
      eval₂ (algebraMap ℚ ℂ) 1 (geometricUniformMomentPolynomial n) /
        (n.factorial : ℂ) := by
  have hfac : qFactorial (1 : ℂ) n ≠ 0 := by
    rw [qFactorial_one_complex]
    exact_mod_cast n.factorial_ne_zero
  have h := eval_geometricUniformMomentRatFunc_of_qFactorial_ne_zero hfac
  rw [qFactorial_one_complex] at h
  exact h

end

end Fabius
