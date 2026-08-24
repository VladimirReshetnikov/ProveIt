import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
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

/-- Evaluation of a Legendre polynomial is smooth. -/
theorem legendrePolynomial_contDiff (n : ℕ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ (legendrePolynomial n).eval x) := by
  induction legendrePolynomial n using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial m a => simpa using contDiff_const.mul (contDiff_id.pow m)

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

private lemma coeff_sq_sub_one_pow_top (n : ℕ) :
    ((X ^ 2 - 1) ^ n : ℝ[X]).coeff (2 * n) = 1 := by
  rw [sq_sub_one_pow_expansion, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [sum_eq_single n]
  · norm_num
  · intro j hj hne
    simp only [ite_eq_right_iff]
    intro h
    omega
  · simp

/-- The leading coefficient of `P_n` in the Rodrigues normalization. -/
theorem coeff_legendrePolynomial_self (n : ℕ) :
    (legendrePolynomial n).coeff n =
      (2 : ℝ)⁻¹ ^ n * (2 * n).choose n := by
  rw [legendrePolynomial, coeff_smul, coeff_iterate_derivative,
    show n + n = 2 * n by omega, coeff_sq_sub_one_pow_top]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_factorial,
    mul_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [inv_pow, mul_inv_rev]
  field_simp
  have hf' : (ascPochhammer ℝ n).eval 1 ≠ 0 := by
    rw [ascPochhammer_eval_one]
    exact hf
  exact mul_div_cancel_left₀ _ hf'

/-- The ordinary Legendre polynomial `P_n` has degree exactly `n`. -/
@[simp] theorem natDegree_legendrePolynomial (n : ℕ) :
    (legendrePolynomial n).natDegree = n := by
  apply le_antisymm
  · calc
      (legendrePolynomial n).natDegree ≤
          (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).natDegree :=
        natDegree_smul_le _ _
      _ ≤ ((X ^ 2 - 1) ^ n : ℝ[X]).natDegree - n :=
        natDegree_iterate_derivative _ _
      _ = n := by
        rw [show (1 : ℝ[X]) = C 1 by simp, natDegree_pow,
          natDegree_X_pow_sub_C]
        omega
  · apply le_natDegree_of_ne_zero
    rw [coeff_legendrePolynomial_self]
    apply mul_ne_zero
    · positivity
    · exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (show n ≤ 2 * n by omega))

/-- Degree form of `natDegree_legendrePolynomial`. -/
@[simp] theorem degree_legendrePolynomial (n : ℕ) :
    (legendrePolynomial n).degree = n := by
  have hp : legendrePolynomial n ≠ 0 := by
    intro h
    have hc := congr_arg (fun p : ℝ[X] ↦ p.coeff n) h
    rw [coeff_legendrePolynomial_self] at hc
    simp only [coeff_zero] at hc
    have hchoose : ((2 * n).choose n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (show n ≤ 2 * n by omega))
    exact (mul_ne_zero (by positivity) hchoose) hc
  rw [degree_eq_natDegree hp, natDegree_legendrePolynomial]

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
  simp only [eval_smul, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]

/-- The ordinary Legendre polynomial has parity equal to its index. -/
theorem eval_legendrePolynomial_neg (n : ℕ) (x : ℝ) :
    (legendrePolynomial n).eval (-x) =
      (-1 : ℝ) ^ n * (legendrePolynomial n).eval x := by
  rw [legendrePolynomial]
  simp only [eval_smul, smul_eq_mul]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [sq_sub_one_pow_expansion, iterate_derivative_sum]
  simp_rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_smul, eval_pow, eval_X, smul_eq_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  by_cases h : n ≤ 2 * j
  · have hprod : (-1 : ℝ) ^ (2 * j - n) * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, Nat.sub_add_cancel h, pow_mul]
      norm_num
    have hsquare : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
      norm_num
    have hparity : (-1 : ℝ) ^ (2 * j - n) = (-1 : ℝ) ^ n := by
      calc
        (-1 : ℝ) ^ (2 * j - n) =
            (-1 : ℝ) ^ (2 * j - n) * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) := by
              rw [hsquare, mul_one]
        _ = ((-1 : ℝ) ^ (2 * j - n) * (-1 : ℝ) ^ n) * (-1 : ℝ) ^ n := by
              ring
        _ = (-1 : ℝ) ^ n := by rw [hprod, one_mul]
    have hx : (-x) ^ (2 * j - n) =
        (-1 : ℝ) ^ (2 * j - n) * x ^ (2 * j - n) := by
      rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
    rw [hx, hparity]
    ring
  · have hzero : (2 * j).descFactorial n = 0 := by
      rw [Nat.descFactorial_eq_zero_iff_lt]
      omega
    simp [hzero]

end Fabius
