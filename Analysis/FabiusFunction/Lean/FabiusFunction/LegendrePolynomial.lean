import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Topology.Algebra.Polynomial

/-!
# Legendre polynomials

This file supplies the ordinary (unshifted) Legendre polynomials needed for
the Fourier--Legendre expansion of Rvachev's `up` function.  Mathlib already
contains the shifted integral polynomials `Polynomial.shiftedLegendre`; the
normalization below is the usual Rodrigues normalization on `[-1,1]`.
Alongside the standard endpoint, parity, norm, and differential-equation
facts, we expose the affine iterated-derivative rule used to relate the
ordinary and shifted bases.
-/

set_option autoImplicit false

open scoped BigOperators Interval Polynomial
open Finset Nat
open Set MeasureTheory

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

/-- Evaluation of a Legendre polynomial is real analytic.  The smoothness
exponent is the top element of `WithTop ℕ∞`, which in this Mathlib is the
*analytic* exponent `ω` rather than `C^∞`; a polynomial is of course both,
and the stronger form is what downstream Legendre arguments consume. -/
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

/-- The Rodrigues normalization fixes the value at the right endpoint. -/
@[simp] theorem eval_legendrePolynomial_one (n : ℕ) :
    (legendrePolynomial n).eval 1 = 1 := by
  have hfactor : ((X ^ 2 - 1) ^ n : ℝ[X]) =
      (X + C (-1)) ^ n * (X + C 1) ^ n := by
    rw [← mul_pow]
    norm_num
    ring
  rw [legendrePolynomial, eval_smul, hfactor, iterate_derivative_mul,
    eval_finsetSum]
  simp_rw [iterate_derivative_X_add_pow]
  rw [sum_eq_single 0]
  · simp only [Nat.choose_zero_right, tsub_zero, Nat.descFactorial_self,
      eval_mul, eval_pow, eval_add, eval_X, eval_C,
      Nat.descFactorial_zero, one_smul,
      smul_eq_mul, Nat.sub_self, pow_zero, nsmul_one]
    rw [show (1 + 1 : ℝ) = 2 by norm_num]
    field_simp
    rw [eval_natCast]
  · intro k hk hk0
    have hk_le : k ≤ n := by simpa using Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show n - (n - k) = k by omega]
    simp [hk0]
  · simp

private lemma rodrigues_derivative_mul_identity (n : ℕ) :
    derivative ((X ^ 2 - 1) ^ n : ℝ[X]) * X ^ 2 -
        derivative ((X ^ 2 - 1) ^ n : ℝ[X]) =
      C (2 * n : ℝ) * (((X ^ 2 - 1) ^ n : ℝ[X]) * X) := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [derivative_pow, derivative_sub, derivative_X, derivative_one,
        sub_zero, mul_one, Nat.cast_succ]
      rw [show n + 1 - 1 = n by omega]
      rw [pow_succ]
      have hc : C (2 * ((n : ℝ) + 1)) = C ((n : ℝ) + 1) * C 2 := by
        rw [← C_mul]
        congr 1
        ring
      rw [hc]
      ring_nf

private lemma rodrigues_sturm_seed (n : ℕ) :
    derivative (derivative ((X ^ 2 - 1) ^ n : ℝ[X])) * X ^ 2 +
          C 2 * (derivative ((X ^ 2 - 1) ^ n : ℝ[X]) * X) -
          derivative (derivative ((X ^ 2 - 1) ^ n : ℝ[X])) =
      C (2 * n : ℝ) *
        (derivative ((X ^ 2 - 1) ^ n : ℝ[X]) * X +
          ((X ^ 2 - 1) ^ n : ℝ[X])) := by
  have h := congrArg derivative (rodrigues_derivative_mul_identity n)
  rw [derivative_sub, derivative_mul, derivative_mul, derivative_mul,
    derivative_C, derivative_X] at h
  simp only [zero_mul, zero_add] at h
  have hx2 : derivative (X ^ 2 : ℝ[X]) = C 2 * X := by
    simp [derivative_pow]
  rw [hx2] at h
  linear_combination h

private lemma rodrigues_sturm_polynomial (n : ℕ) :
    derivative^[n + 2] ((X ^ 2 - 1) ^ n : ℝ[X]) * (X ^ 2 - 1) +
        C 2 * X * derivative^[n + 1] ((X ^ 2 - 1) ^ n : ℝ[X]) -
        C (n * (n + 1) : ℝ) * derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X]) = 0 := by
  cases n with
  | zero => norm_num
  | succ m =>
    let f : ℝ[X] := (X ^ 2 - 1) ^ (m + 1)
    have hseed : derivative (derivative f) * X ^ 2 +
          C 2 * (derivative f * X) - derivative (derivative f) =
        C (2 * ((m : ℝ) + 1)) * (derivative f * X + f) := by
      simpa [f, Nat.cast_add, Nat.cast_one] using rodrigues_sturm_seed (m + 1)
    have h := congrArg (fun p : ℝ[X] ↦ derivative^[m + 1] p) hseed
    have htwo : derivative (derivative f) = derivative^[2] f := by
      simp [Function.iterate_succ_apply]
    have hone : derivative f = derivative^[1] f := by simp
    have hcomp2 : derivative^[m + 1] (derivative^[2] f) =
        derivative^[m + 3] f := by
      rw [← Function.iterate_add_apply]
    have hcomp1 : derivative^[m + 1] (derivative f) =
        derivative^[m + 2] f := by
      rw [hone]
      rw [← Function.iterate_add_apply]
    have hcomp0 : derivative^[m] (derivative f) =
        derivative^[m + 1] f := by
      rw [hone]
      rw [← Function.iterate_add_apply]
    rw [htwo] at h
    rw [iterate_derivative_sub,
      iterate_map_add derivative,
      iterate_derivative_derivative_mul_X_sq,
      iterate_derivative_C_mul,
      iterate_derivative_derivative_mul_X,
      hcomp2,
      iterate_derivative_C_mul,
      iterate_map_add derivative,
      iterate_derivative_mul_X,
      hcomp1,
      show m + 1 - 1 = m by omega,
      hcomp0] at h
    simp only [Nat.add_assoc] at h
    dsimp only [f] at h
    simp only [nsmul_eq_mul, C_mul] at h
    simp only [Nat.add_assoc] at h ⊢
    push_cast at h ⊢
    simp only [C_add, C_mul, map_one, map_ofNat, ← C_eq_natCast] at h ⊢
    linear_combination h

/-- Polynomial form of the Legendre Sturm--Liouville equation. -/
theorem legendrePolynomial_sturm_polynomial (n : ℕ) :
    derivative (derivative (legendrePolynomial n)) * (X ^ 2 - 1) +
        C 2 * X * derivative (legendrePolynomial n) =
      C (n * (n + 1) : ℝ) * legendrePolynomial n := by
  rw [legendrePolynomial]
  simp only [derivative_smul]
  have h := rodrigues_sturm_polynomial n
  have hcomp1 : derivative (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])) =
      derivative^[n + 1] ((X ^ 2 - 1) ^ n : ℝ[X]) := by
    simpa [Nat.succ_eq_add_one] using
      (Function.iterate_succ_apply' derivative n
        ((X ^ 2 - 1) ^ n : ℝ[X])).symm
  have hcomp2 : derivative (derivative^[n + 1] ((X ^ 2 - 1) ^ n : ℝ[X])) =
      derivative^[n + 2] ((X ^ 2 - 1) ^ n : ℝ[X]) := by
    simpa [Nat.succ_eq_add_one] using
      (Function.iterate_succ_apply' derivative (n + 1)
        ((X ^ 2 - 1) ^ n : ℝ[X])).symm
  rw [hcomp1, hcomp2]
  simp only [Polynomial.smul_eq_C_mul]
  linear_combination C ((2 ^ n * (n.factorial : ℝ))⁻¹) * h

/-- Pointwise Sturm--Liouville eigenvalue equation for `P_n`. -/
theorem legendrePolynomial_sturm_liouville (n : ℕ) (x : ℝ) :
    -deriv (fun y : ℝ ↦
        (1 - y ^ 2) * deriv (fun z : ℝ ↦ (legendrePolynomial n).eval z) y) x =
      (n * (n + 1) : ℝ) * (legendrePolynomial n).eval x := by
  have h := congrArg (fun p : ℝ[X] ↦ p.eval x)
    (legendrePolynomial_sturm_polynomial n)
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_C] at h
  simp_rw [Polynomial.deriv]
  have hfun : (fun y : ℝ ↦
      (1 - y ^ 2) * (legendrePolynomial n).derivative.eval y) =
      fun y : ℝ ↦ ((1 - X ^ 2) * derivative (legendrePolynomial n)).eval y := by
    funext y
    simp
  rw [hfun, Polynomial.deriv]
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_pow,
    derivative_X, mul_one, eval_add, eval_mul, eval_sub, eval_pow,
    eval_X, eval_one, eval_C, eval_zero]
  linear_combination h

private lemma rodrigues_derivative_endpoint_zero
    (n j : ℕ) (hj : j < n) (x : ℝ) (hx : x ^ 2 = 1) :
    (derivative^[j] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x = 0 := by
  have hdvd := pow_sub_dvd_iterate_derivative_pow
    (X ^ 2 - 1 : ℝ[X]) n j
  rcases hdvd with ⟨r, hr⟩
  rw [hr, eval_mul, eval_pow]
  have hbase : (X ^ 2 - 1 : ℝ[X]).eval x = 0 := by
    simp [hx]
  rw [hbase, zero_pow (Nat.sub_pos_of_lt hj).ne', zero_mul]

private lemma hasDerivAt_eval_iterate_derivative
    (p : ℝ[X]) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (derivative^[j] p).eval y)
      ((derivative^[j + 1] p).eval x) x := by
  simpa only [Function.iterate_succ_apply'] using
    (derivative^[j] p).hasDerivAt x

private lemma rodrigues_integral_step (n r : ℕ) (hr : r < n) :
    (∫ x in (-1 : ℝ)..1,
      (derivative^[n - r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
        (derivative^[n + r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) =
      -∫ x in (-1 : ℝ)..1,
        (derivative^[n - (r + 1)] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
          (derivative^[n + (r + 1)] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x := by
  let p : ℝ[X] := (X ^ 2 - 1) ^ n
  let u : ℝ → ℝ := fun x ↦ (derivative^[n + r] p).eval x
  let u' : ℝ → ℝ := fun x ↦ (derivative^[n + r + 1] p).eval x
  let v : ℝ → ℝ := fun x ↦ (derivative^[n - r - 1] p).eval x
  let v' : ℝ → ℝ := fun x ↦ (derivative^[n - r] p).eval x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    dsimp [u, u']
    exact hasDerivAt_eval_iterate_derivative p (n + r) x
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp [v, v']
    simpa only [show n - r - 1 + 1 = n - r by omega] using
      hasDerivAt_eval_iterate_derivative p (n - r - 1) x
  have huInt : IntervalIntegrable u' volume (-1 : ℝ) 1 := by
    exact (derivative^[n + r + 1] p).continuous.intervalIntegrable _ _
  have hvInt : IntervalIntegrable v' volume (-1 : ℝ) 1 := by
    exact (derivative^[n - r] p).continuous.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _hx ↦ hu x) (fun x _hx ↦ hv x) huInt hvInt
  have hvOne : v 1 = 0 := by
    exact rodrigues_derivative_endpoint_zero n (n - r - 1) (by omega) 1 (by norm_num)
  have hvNegOne : v (-1) = 0 := by
    exact rodrigues_derivative_endpoint_zero n (n - r - 1) (by omega) (-1) (by norm_num)
  rw [hvOne, hvNegOne, mul_zero, mul_zero, sub_zero, zero_sub] at hparts
  dsimp [u, u', v, v', p] at hparts ⊢
  rw [show n - r - 1 = n - (r + 1) by omega] at hparts
  calc
    (∫ x in (-1 : ℝ)..1,
      (derivative^[n - r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
        (derivative^[n + r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) =
        ∫ x in (-1 : ℝ)..1,
          (derivative^[n + r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
            (derivative^[n - r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x := by
              apply intervalIntegral.integral_congr
              intro x _hx
              ring
    _ = -∫ x in (-1 : ℝ)..1,
        (derivative^[n - (r + 1)] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
          (derivative^[n + (r + 1)] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x := by
            rw [hparts]
            congr 2
            funext x
            rw [← Function.iterate_succ_apply]
            rw [show (n + r).succ = n + (r + 1) by omega]
            ring

private lemma rodrigues_integral_shift (n r : ℕ) (hr : r ≤ n) :
    (∫ x in (-1 : ℝ)..1,
      (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
        (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) =
      (-1 : ℝ) ^ r *
        ∫ x in (-1 : ℝ)..1,
          (derivative^[n - r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
            (derivative^[n + r] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrle : r ≤ n := by omega
      have hrlt : r < n := by omega
      rw [ih hrle]
      rw [rodrigues_integral_step n r hrlt]
      rw [pow_succ]
      ring

private lemma rodrigues_integral_by_parts (n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
        (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) =
      (-1 : ℝ) ^ n *
        ∫ x in (-1 : ℝ)..1,
          ((X ^ 2 - 1) ^ n : ℝ[X]).eval x *
            (derivative^[2 * n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x := by
  simpa [two_mul] using rodrigues_integral_shift n n le_rfl

private lemma iterate_derivative_twice_rodrigues (n : ℕ) :
    derivative^[2 * n] ((X ^ 2 - 1) ^ n : ℝ[X]) =
      ((2 * n).factorial : ℝ[X]) := by
  have hbaseMonic : (X ^ 2 - 1 : ℝ[X]).Monic := by
    simpa using
      (monic_X_pow_sub_C (1 : ℝ) (by norm_num : (2 : ℕ) ≠ 0))
  have hmonic : ((X ^ 2 - 1) ^ n : ℝ[X]).Monic := hbaseMonic.pow n
  have hbaseDegree : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
    change (X ^ 2 - C (1 : ℝ)).natDegree = 2
    exact natDegree_X_pow_sub_C
  have hdegree : ((X ^ 2 - 1) ^ n : ℝ[X]).natDegree = 2 * n := by
    rw [hbaseMonic.natDegree_pow, hbaseDegree]
    omega
  ext k
  by_cases hk : k = 0
  · subst k
    rw [coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self]
    have htop : ((X ^ 2 - 1) ^ n : ℝ[X]).coeff (2 * n) = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    rw [htop]
    simp
  · rw [coeff_iterate_derivative]
    rw [coeff_eq_zero_of_natDegree_lt (by rw [hdegree]; omega)]
    simp [hk]

private noncomputable def legendreWeightIntegral (n : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ n

@[simp] private lemma legendreWeightIntegral_zero :
    legendreWeightIntegral 0 = 2 := by
  norm_num [legendreWeightIntegral]

private lemma legendreWeightIntegral_recurrence (n : ℕ) :
    (((2 * n + 3 : ℕ) : ℝ)) * legendreWeightIntegral (n + 1) =
      2 * ((n + 1 : ℕ) : ℝ) * legendreWeightIntegral n := by
  let u : ℝ → ℝ := fun x ↦ x
  let u' : ℝ → ℝ := fun _ ↦ 1
  let v : ℝ → ℝ := fun x ↦ (1 - x ^ 2) ^ (n + 1)
  let v' : ℝ → ℝ := fun x ↦
    -2 * (n + 1 : ℝ) * x * (1 - x ^ 2) ^ n
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    dsimp [u, u']
    exact hasDerivAt_id x
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp [v, v']
    have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    have hp := hinner.pow (n + 1)
    change HasDerivAt (fun y : ℝ ↦ (1 - y ^ 2) ^ (n + 1)) _ x at hp
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hp
    convert hp using 1
    ring
  have huInt : IntervalIntegrable u' volume (-1 : ℝ) 1 := by
    exact continuous_const.intervalIntegrable _ _
  have hvInt : IntervalIntegrable v' volume (-1 : ℝ) 1 := by
    exact (by fun_prop : Continuous v').intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _hx ↦ hu x) (fun x _hx ↦ hv x) huInt hvInt
  have hmain :
      2 * (n + 1 : ℝ) *
          (∫ x in (-1 : ℝ)..1, x ^ 2 * (1 - x ^ 2) ^ n) =
        legendreWeightIntegral (n + 1) := by
    dsimp [u, u', v, v'] at hparts
    norm_num at hparts
    rw [← intervalIntegral.integral_const_mul]
    convert hparts using 1
    · apply intervalIntegral.integral_congr
      intro x _hx
      ring
    · simp [legendreWeightIntegral]
  have hdecompose :
      (∫ x in (-1 : ℝ)..1, x ^ 2 * (1 - x ^ 2) ^ n) =
        legendreWeightIntegral n - legendreWeightIntegral (n + 1) := by
    unfold legendreWeightIntegral
    rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun x : ℝ ↦ (1 - x ^ 2) ^ n)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ ↦ (1 - x ^ 2) ^ (n + 1))).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro x _hx
    change x ^ 2 * (1 - x ^ 2) ^ n =
      (1 - x ^ 2) ^ n - (1 - x ^ 2) ^ (n + 1)
    rw [pow_succ]
    ring
  rw [hdecompose] at hmain
  push_cast
  linear_combination -hmain

private lemma legendreWeightIntegral_closed (n : ℕ) :
    legendreWeightIntegral n =
      (2 : ℝ) ^ (2 * n + 1) * (n.factorial : ℝ) ^ 2 /
        ((2 * n + 1).factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hden : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hden
      rw [legendreWeightIntegral_recurrence n, ih]
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
      norm_num
      rw [show (2 * n + 1) + 2 = (2 * n + 2) + 1 by omega,
        Nat.factorial_succ (2 * n + 2)]
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ (2 * n + 1)]
      rw [Nat.factorial_succ n]
      push_cast
      field_simp
      ring

private lemma rodrigues_sq_integral_eq_weight (n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
        (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) =
      ((2 * n).factorial : ℝ) * legendreWeightIntegral n := by
  rw [rodrigues_integral_by_parts, iterate_derivative_twice_rodrigues]
  simp only [eval_pow, eval_sub, eval_X, eval_one, eval_natCast]
  unfold legendreWeightIntegral
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  change (-1 : ℝ) ^ n * ((x ^ 2 - 1) ^ n * ((2 * n).factorial : ℝ)) =
    ((2 * n).factorial : ℝ) * (1 - x ^ 2) ^ n
  rw [show x ^ 2 - 1 = -(1 - x ^ 2) by ring]
  have hneg : (-(1 - x ^ 2)) ^ n =
      (-1 : ℝ) ^ n * (1 - x ^ 2) ^ n := by
    rw [show -(1 - x ^ 2) = (-1 : ℝ) * (1 - x ^ 2) by ring, mul_pow]
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
    norm_num
  rw [hneg]
  calc
    (-1 : ℝ) ^ n *
        (((-1 : ℝ) ^ n * (1 - x ^ 2) ^ n) * ((2 * n).factorial : ℝ)) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        ((2 * n).factorial : ℝ) * (1 - x ^ 2) ^ n := by ring
    _ = ((2 * n).factorial : ℝ) * (1 - x ^ 2) ^ n := by rw [hsign]; ring

/-- Squared `L²[-1,1]` norm of the ordinary Legendre polynomial. -/
theorem integral_sq_eval_legendrePolynomial (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ((legendrePolynomial n).eval x) ^ 2) =
      2 / (((2 * n + 1 : ℕ) : ℝ)) := by
  rw [legendrePolynomial]
  simp only [eval_smul, smul_eq_mul]
  have hpointwise :
      (∫ x in (-1 : ℝ)..1,
        (((2 : ℝ) ^ n * (n.factorial : ℝ))⁻¹ *
          (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) ^ 2) =
        (((2 : ℝ) ^ n * (n.factorial : ℝ))⁻¹) ^ 2 *
          (∫ x in (-1 : ℝ)..1,
            (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x *
              (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hpointwise, rodrigues_sq_integral_eq_weight,
    legendreWeightIntegral_closed]
  rw [Nat.factorial_succ (2 * n)]
  push_cast
  field_simp
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

/-- Polynomial form of the parity identity for the ordinary Legendre basis. -/
theorem legendrePolynomial_comp_neg_X (n : ℕ) :
    (legendrePolynomial n).comp (-X) =
      (-1 : ℝ) ^ n • legendrePolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_univ.mono
  intro x _hx
  simp only [Set.mem_setOf_eq, eval_comp, eval_neg, eval_X, eval_smul,
    smul_eq_mul]
  exact eval_legendrePolynomial_neg n x

/-- Value of the ordinary Legendre polynomial at the left endpoint. -/
@[simp] theorem eval_legendrePolynomial_neg_one (n : ℕ) :
    (legendrePolynomial n).eval (-1) = (-1 : ℝ) ^ n := by
  simpa using eval_legendrePolynomial_neg n 1

/-! ## Translation to the shifted Legendre normalization -/

/-- Iterated polynomial differentiation through an affine substitution. -/
theorem iterate_derivative_comp_affine
    (p : ℝ[X]) (a b : ℝ) (n : ℕ) :
    derivative^[n] (p.comp (C a * X + C b)) =
      a ^ n • (derivative^[n] p).comp (C a * X + C b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        derivative_smul, derivative_comp]
      simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
        zero_mul, mul_one, zero_add]
      rw [pow_succ]
      simp [smul_eq_C_mul]
      ring

/-- The ordinary and shifted Legendre conventions agree after the affine
change of variables `x ↦ 1 - 2x`.  Mathlib's `shiftedLegendre` has integer
coefficients, so its right-hand side is mapped coefficientwise to `ℝ`. -/
theorem legendrePolynomial_comp_one_sub_two_X (n : ℕ) :
    (legendrePolynomial n).comp (1 - C 2 * X) =
      (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ) := by
  apply mul_left_cancel₀ (show C (n.factorial : ℝ) ≠ 0 by
    rw [C_ne_zero]
    exact_mod_cast Nat.factorial_ne_zero n)
  rw [show C (n.factorial : ℝ) *
      (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ) =
      derivative^[n] (X ^ n * (1 - X) ^ n : ℝ[X]) by
    have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
      (Polynomial.factorial_mul_shiftedLegendre_eq n)
    rw [← Polynomial.iterate_derivative_map] at h
    simpa using h]
  rw [legendrePolynomial, smul_comp]
  have hcompose :
      (((X ^ 2 - 1) ^ n : ℝ[X]).comp (1 - C 2 * X)) =
        (-4 : ℝ) ^ n • (X ^ n * (1 - X) ^ n : ℝ[X]) := by
    simp
    rw [← mul_pow, ← smul_pow]
    simp only [smul_eq_C_mul, map_neg, map_ofNat]
    ring
  have hderiv := iterate_derivative_comp_affine
    ((X ^ 2 - 1) ^ n : ℝ[X]) (-2) 1 n
  rw [show C (-2 : ℝ) * X + C 1 = 1 - C 2 * X by
    simp only [map_neg, map_ofNat, C_1]
    ring] at hderiv
  have hscaled := congrArg (fun p : ℝ[X] ↦ derivative^[n] p) hcompose
  rw [Polynomial.iterate_derivative_smul] at hscaled
  rw [hderiv] at hscaled
  calc
    C (n.factorial : ℝ) * (2 ^ n * (n.factorial : ℝ))⁻¹ •
        (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).comp (1 - C 2 * X) =
      ((-4 : ℝ) ^ n)⁻¹ •
        ((-2 : ℝ) ^ n •
          (derivative^[n] ((X ^ 2 - 1) ^ n : ℝ[X])).comp (1 - C 2 * X)) := by
        simp only [smul_eq_C_mul]
        repeat' rw [← mul_assoc]
        rw [← C_mul, ← C_mul]
        congr 2
        field_simp
        rw [← mul_pow]
        norm_num
    _ = ((-4 : ℝ) ^ n)⁻¹ •
        ((-4 : ℝ) ^ n •
          derivative^[n] (X ^ n * (1 - X) ^ n : ℝ[X])) := by rw [hscaled]
    _ = derivative^[n] (X ^ n * (1 - X) ^ n : ℝ[X]) := by
      rw [smul_smul]
      field_simp
      simp

/-- The translated even Legendre polynomial in increasing monomial order:
`P_(2n)(x - 1) = ∑_{j=0}^{2n} (-1)^j 2⁻ʲ C(2n,j) C(2n+j,j) x^j`. -/
theorem eval_legendrePolynomial_even_sub_one (n : ℕ) (x : ℝ) :
    (legendrePolynomial (2 * n)).eval (x - 1) =
      ∑ j ∈ range (2 * n + 1),
        (-1 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j *
          (2 * n).choose j * (j + 2 * n).choose j * x ^ j := by
  have hcomp := congrArg (fun p : ℝ[X] ↦ p.eval (x / 2))
    (legendrePolynomial_comp_one_sub_two_X (2 * n))
  have hparity := eval_legendrePolynomial_neg (2 * n) (1 - x)
  have hleft : (legendrePolynomial (2 * n)).eval (x - 1) =
      (legendrePolynomial (2 * n)).eval (1 - x) := by
    rw [show x - 1 = -(1 - x) by ring, hparity]
    rw [pow_mul]
    norm_num
  rw [hleft]
  simp only [eval_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X,
    eval_map, Polynomial.shiftedLegendre, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X] at hcomp
  rw [show 1 - 2 * (x / 2) = 1 - x by ring] at hcomp
  rw [hcomp]
  apply sum_congr rfl
  intro j hj
  rw [show (2 * n + j).choose (2 * n) = (j + 2 * n).choose j by
    simpa [add_comm] using
      (Nat.choose_symm_add (a := j) (b := 2 * n)).symm]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [div_pow, div_eq_mul_inv, inv_pow]
  ring

end Fabius
