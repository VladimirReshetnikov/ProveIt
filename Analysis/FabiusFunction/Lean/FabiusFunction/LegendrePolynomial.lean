import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# Legendre polynomials

This file supplies the ordinary (unshifted) Legendre polynomials needed for
the Fourier--Legendre expansion of Rvachev's `up` function.  Mathlib already
contains the shifted integral polynomials `Polynomial.shiftedLegendre`; the
normalization below is the usual Rodrigues normalization on `[-1,1]`.
-/

set_option autoImplicit false

open scoped BigOperators Interval Polynomial
open Finset Nat

namespace Fabius

open Polynomial

/-- The ordinary Legendre polynomial, in Rodrigues normalization:
`P_n = (2^n n!)⁻¹ D^n (X² - 1)^n`. -/
noncomputable def legendrePolynomial (n : ℕ) : ℝ[X] :=
  ((2 : ℝ) ^ n * (n.factorial : ℝ))⁻¹ •
    derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])

@[simp] theorem legendrePolynomial_zero : legendrePolynomial 0 = 1 := by
  simp [legendrePolynomial]

@[simp] theorem legendrePolynomial_one : legendrePolynomial 1 = X := by
  ext k
  norm_num [legendrePolynomial, derivative_sub, coeff_X]

private lemma sq_sub_one_pow_expansion (N : ℕ) :
    ((X ^ 2 - 1) ^ N : ℝ[X]) =
      ∑ j ∈ range (N + 1),
        C (((-1 : ℝ) ^ (N + j)) * N.choose j) * X ^ (2 * j) := by
  rw [sub_eq_add_neg, add_pow]
  congr! 1 with j hj
  have hjle : j ≤ N := by simpa using Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hsign : (-1 : ℝ) ^ (N - j) = (-1 : ℝ) ^ (N + j) := by
    rw [show N + j = (N - j) + 2 * j by omega, pow_add, pow_mul]
    norm_num
  rw [← pow_mul]
  rw [show (-1 : ℝ[X]) ^ (N - j) = C ((-1 : ℝ) ^ (N - j)) by simp,
    hsign]
  simp only [C_mul, ← C_eq_natCast]
  ring

private lemma iterate_derivative_sq_sub_one_even (n : ℕ) :
    derivative^[2 * n] ((X ^ 2 - 1) ^ (2 * n) : ℝ[X]) =
      ((2 * n).factorial : ℝ) •
        ∑ k ∈ range (n + 1),
          C (((-1 : ℝ) ^ (n + k)) *
              (2 * n).choose (n + k) *
              (2 * n + 2 * k).choose (2 * n)) * X ^ (2 * k) := by
  rw [sq_sub_one_pow_expansion, iterate_derivative_sum]
  simp_rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul]
  rw [show 2 * n + 1 = n + (n + 1) by omega, sum_range_add]
  rw [sum_eq_zero (fun j hj => by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by
      have := mem_range.mp hj
      omega)]
    simp), zero_add]
  rw [smul_sum]
  apply sum_congr rfl
  intro k hk
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Nat.cast_mul]
  rw [show 2 * (n + k) - 2 * n = 2 * k by omega]
  rw [show 2 * (n + k) = 2 * n + 2 * k by omega]
  have hsign : (-1 : ℝ) ^ (2 * n + (n + k)) = (-1 : ℝ) ^ (n + k) := by
    rw [show 2 * n + (n + k) = (n + k) + 2 * n by omega, pow_add, pow_mul]
    norm_num
  rw [hsign]
  simp only [Polynomial.smul_eq_C_mul, C_mul]
  ring

/-- The monomial formula for an even Legendre polynomial.  It is arranged in
the increasing-power order used by the Fabius coefficient formula. -/
theorem legendrePolynomial_even_explicit (n : ℕ) :
    legendrePolynomial (2 * n) =
      (4 : ℝ)⁻¹ ^ n •
        ∑ k ∈ range (n + 1),
          C (((-1 : ℝ) ^ (n + k)) *
              (2 * n).choose (n + k) *
              (2 * n + 2 * k).choose (2 * n)) * X ^ (2 * k) := by
  rw [legendrePolynomial, iterate_derivative_sq_sub_one_even]
  rw [smul_smul]
  congr 1
  rw [show (2 : ℝ) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]
  have hf : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← mul_pow]
  norm_num

/-- Pointwise form of `legendrePolynomial_even_explicit`. -/
theorem eval_legendrePolynomial_even (n : ℕ) (x : ℝ) :
    (legendrePolynomial (2 * n)).eval x =
      (4 : ℝ)⁻¹ ^ n *
        ∑ k ∈ range (n + 1),
          ((-1 : ℝ) ^ (n + k)) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) * x ^ (2 * k) := by
  rw [legendrePolynomial_even_explicit]
  simp only [eval_smul, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]

end Fabius
