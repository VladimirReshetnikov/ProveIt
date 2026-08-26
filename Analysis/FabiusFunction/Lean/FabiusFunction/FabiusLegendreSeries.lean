import FabiusFunction.FabiusLegendreCoefficients
import FabiusFunction.LegendreSeriesConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Fourier--Legendre series of Rvachev's up function

This file combines the exact coefficient evaluation with the analytic
convergence theorem.  The expansion is understood on the natural Legendre
interval `[-1, 1]`; convergence there is absolute and uniform, and therefore
also pointwise at both endpoints.  We record the complete orthogonality
formula and absolute summability of both the full coefficient sequence and
its even subsequence.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Interval Polynomial
open Set MeasureTheory

namespace Fabius

noncomputable section

open Polynomial

/-! ## Orthogonality from the Sturm--Liouville equation -/

/-- Distinct members of a smooth polynomial eigenfamily for the Legendre
Sturm--Liouville operator are orthogonal on `[-1,1]`. -/
theorem integral_eigenpolynomial_mul_eq_zero_of_ne
    (P : ℕ → ℝ[X])
    (hpSmooth : ∀ n, ContDiff ℝ ∞ (fun x : ℝ ↦ (P n).eval x))
    (hpEigen : ∀ n x,
      legendreSturmLiouville (fun y : ℝ ↦ (P n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (P n).eval x)
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in (-1 : ℝ)..1, (P m).eval x * (P n).eval x) = 0 := by
  let I : ℝ := ∫ x in (-1 : ℝ)..1, (P m).eval x * (P n).eval x
  have htransfer := eigenvalue_mul_integral_eq_integral_legendreSturmLiouville
    (hpSmooth m) (hpSmooth n) ((n : ℝ) * (n + 1 : ℝ)) (hpEigen n)
  have heq :
      ((n : ℝ) * (n + 1 : ℝ)) * I =
        ((m : ℝ) * (m + 1 : ℝ)) * I := by
    calc
      ((n : ℝ) * (n + 1 : ℝ)) * I =
          ∫ x in (-1 : ℝ)..1,
            legendreSturmLiouville (fun y : ℝ ↦ (P m).eval y) x *
              (P n).eval x := by simpa [I] using htransfer
      _ = ∫ x in (-1 : ℝ)..1,
            ((m : ℝ) * (m + 1 : ℝ)) *
              ((P m).eval x * (P n).eval x) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only
        rw [hpEigen m x]
        ring
      _ = ((m : ℝ) * (m + 1 : ℝ)) * I := by
        rw [intervalIntegral.integral_const_mul]
  have heigenNe :
      (n : ℝ) * (n + 1 : ℝ) ≠ (m : ℝ) * (m + 1 : ℝ) := by
    intro heigenEq
    rcases lt_or_gt_of_ne hmn with hmnlt | hnmLt
    · have hmnlt' : (m : ℝ) < n := by exact_mod_cast hmnlt
      have hm0 : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    · have hnmLt' : (n : ℝ) < m := by exact_mod_cast hnmLt
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
  have hproduct :
      ((n : ℝ) * (n + 1 : ℝ) - (m : ℝ) * (m + 1 : ℝ)) * I = 0 := by
    linarith
  change I = 0
  exact (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr heigenNe)

/-! ## Specialization to Rvachev's up function -/

/-- The generic normalized coefficient functional of
`LegendreSeriesConvergence`, applied to `rvachevUp F` and to the `n`-th
ordinary Legendre polynomial, is by definition
`rvachevFullLegendreCoefficient F n`.  This is the notation bridge used to
rewrite in `summable_abs_rvachevFullLegendreCoefficient`,
`hasSum_rvachevFullLegendreSeries`,
`hasSum_rvachevFullLegendreSeries_uniform`, and in
`legendreProjectionPolynomial_rvachevUp` of
`FabiusLegendreLeastSquares`. -/
@[simp]
theorem legendreSeriesCoefficientOf_rvachevUp
    (F : BoundedFabius) (n : ℕ) :
    legendreSeriesCoefficientOf (rvachevUp F)
        (fun x : ℝ ↦ (legendrePolynomial n).eval x) n =
      rvachevFullLegendreCoefficient F n := by
  rfl

private theorem legendrePolynomial_contDiff_infty (n : ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ (legendrePolynomial n).eval x) :=
  (legendrePolynomial_contDiff n).of_le (by simp)

/-- The pointwise Sturm--Liouville equation in the notation used by the
generic convergence layer. -/
theorem legendreSturmLiouville_eval_legendrePolynomial (n : ℕ) (x : ℝ) :
    legendreSturmLiouville
        (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
      ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x := by
  simpa only [legendreSturmLiouville] using
    legendrePolynomial_sturm_liouville n x

/-- Distinct ordinary Legendre polynomials are orthogonal on `[-1,1]`. -/
theorem integral_eval_legendrePolynomial_mul_eq_zero_of_ne
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in (-1 : ℝ)..1,
      (legendrePolynomial m).eval x * (legendrePolynomial n).eval x) = 0 := by
  exact integral_eigenpolynomial_mul_eq_zero_of_ne legendrePolynomial
    legendrePolynomial_contDiff_infty
    legendreSturmLiouville_eval_legendrePolynomial hmn

/-- Complete orthogonality formula for the ordinary Legendre basis, including
the diagonal normalization. -/
theorem integral_eval_legendrePolynomial_mul (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (legendrePolynomial m).eval x * (legendrePolynomial n).eval x) =
      if m = n then 2 / (((2 * n + 1 : ℕ) : ℝ)) else 0 := by
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    convert integral_sq_eval_legendrePolynomial n using 1
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  · rw [if_neg hmn, integral_eval_legendrePolynomial_mul_eq_zero_of_ne hmn]

/-- The ordinary Legendre polynomial has absolute value at most one on its
natural interval. -/
theorem abs_eval_legendrePolynomial_le_one (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(legendrePolynomial n).eval x| ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
      apply abs_eval_le_one_of_legendre_ode
        (legendrePolynomial (n + 1)) (n + 1) (by omega) ?_ ?_ ?_ x hx
      · intro z
        have h := congrArg (fun p : ℝ[X] ↦ p.eval z)
          (legendrePolynomial_sturm_polynomial (n + 1))
        simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one,
          eval_C] at h
        linear_combination -h
      · rw [eval_legendrePolynomial_neg_one, pow_two, ← pow_add,
          show (n + 1) + (n + 1) = 2 * (n + 1) by omega, pow_mul]
        norm_num
      · simp

/-- The full Fourier--Legendre coefficient sequence of Rvachev's smooth
function is absolutely summable. -/
theorem summable_abs_rvachevFullLegendreCoefficient
    (F : BoundedFabius) (hF : IsFabius F) :
    Summable (fun n ↦ |rvachevFullLegendreCoefficient F n|) := by
  simpa only [legendreSeriesCoefficientOf_rvachevUp] using
    summable_abs_legendreSeriesCoefficientOf
      (rvachevUp F) (rvachev_contDiff F hF)
      (fun n x ↦ (legendrePolynomial n).eval x)
      legendrePolynomial_contDiff_infty
      legendreSturmLiouville_eval_legendrePolynomial
      abs_eval_legendrePolynomial_le_one

/-- The even coefficient sequence used in the displayed Rvachev--Legendre
series is absolutely summable. -/
theorem summable_abs_rvachevLegendreCoefficient
    (F : BoundedFabius) (hF : IsFabius F) :
    Summable (fun n ↦ |rvachevLegendreCoefficient F n|) := by
  have h := (summable_abs_rvachevFullLegendreCoefficient F hF).comp_injective
    (mul_right_injective₀ (two_ne_zero' ℕ))
  exact h.congr (fun n ↦ by
    change |rvachevFullLegendreCoefficient F (2 * n)| =
      |rvachevLegendreCoefficient F n|
    rw [rvachevFullLegendreCoefficient_even_eq])

/-- The full Fourier--Legendre series of Rvachev's up function converges
pointwise on `[-1,1]`, including both endpoints. -/
theorem hasSum_rvachevFullLegendreSeries
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦
      rvachevFullLegendreCoefficient F n * (legendrePolynomial n).eval x)
      (rvachevUp F x) := by
  simpa only [legendreSeriesCoefficientOf_rvachevUp] using
    hasSum_legendrePolynomialSeries_eq
      (rvachevUp F) (rvachev_contDiff F hF) legendrePolynomial
      degree_legendrePolynomial legendrePolynomial_contDiff_infty
      legendreSturmLiouville_eval_legendrePolynomial
      abs_eval_legendrePolynomial_le_one
      (fun _ _ hmn ↦ integral_eval_legendrePolynomial_mul_eq_zero_of_ne hmn)
      integral_sq_eval_legendrePolynomial x hx

/-- Tsum form of `hasSum_rvachevFullLegendreSeries`. -/
theorem tsum_rvachevFullLegendreSeries
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∑' n,
      rvachevFullLegendreCoefficient F n * (legendrePolynomial n).eval x) =
      rvachevUp F x :=
  (hasSum_rvachevFullLegendreSeries F hF x hx).tsum_eq

/-- The full Fourier--Legendre series converges uniformly on `[-1,1]`.
The `ContinuousMap` norm is the supremum norm on that compact interval. -/
theorem hasSum_rvachevFullLegendreSeries_uniform
    (F : BoundedFabius) (hF : IsFabius F) :
    HasSum (fun n ↦
      rvachevFullLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial n).eval x)
          (legendrePolynomial_contDiff n).continuous)
      (continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous) := by
  simpa only [legendreSeriesCoefficientOf_rvachevUp] using
    hasSum_legendrePolynomialSeries_eq_uniform
      (rvachevUp F) (rvachev_contDiff F hF) legendrePolynomial
      degree_legendrePolynomial legendrePolynomial_contDiff_infty
      legendreSturmLiouville_eval_legendrePolynomial
      abs_eval_legendrePolynomial_le_one
      (fun _ _ hmn ↦ integral_eval_legendrePolynomial_mul_eq_zero_of_ne hmn)
      integral_sq_eval_legendrePolynomial

/-- Tsum form of `hasSum_rvachevFullLegendreSeries_uniform`. -/
theorem tsum_rvachevFullLegendreSeries_uniform
    (F : BoundedFabius) (hF : IsFabius F) :
    (∑' n,
      rvachevFullLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial n).eval x)
          (legendrePolynomial_contDiff n).continuous) =
      continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous :=
  (hasSum_rvachevFullLegendreSeries_uniform F hF).tsum_eq

/-- Since Rvachev's up function is even, its Legendre series contains only
the even-indexed polynomials. -/
theorem hasSum_rvachevLegendreSeries
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦
      rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x) (rvachevUp F x) := by
  have heven := hasSum_even_of_odd_eq_zero
    (hasSum_rvachevFullLegendreSeries F hF x hx) (fun n ↦ by
      rw [rvachevFullLegendreCoefficient_odd_eq_zero F hF n, zero_mul])
  simpa only [rvachevFullLegendreCoefficient_even_eq] using heven

/-- Tsum form of `hasSum_rvachevLegendreSeries`. -/
theorem tsum_rvachevLegendreSeries
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∑' n,
      rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x) = rvachevUp F x :=
  (hasSum_rvachevLegendreSeries F hF x hx).tsum_eq

/-- The even-only Legendre series converges uniformly on `[-1,1]`. -/
theorem hasSum_rvachevLegendreSeries_uniform
    (F : BoundedFabius) (hF : IsFabius F) :
    HasSum (fun n ↦
      rvachevLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous)
      (continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous) := by
  have heven := hasSum_even_of_odd_eq_zero
    (hasSum_rvachevFullLegendreSeries_uniform F hF) (fun n ↦ by
      rw [rvachevFullLegendreCoefficient_odd_eq_zero F hF n, zero_smul])
  simpa only [rvachevFullLegendreCoefficient_even_eq] using heven

/-- Tsum form of `hasSum_rvachevLegendreSeries_uniform`. -/
theorem tsum_rvachevLegendreSeries_uniform
    (F : BoundedFabius) (hF : IsFabius F) :
    (∑' n,
      rvachevLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous) =
      continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous :=
  (hasSum_rvachevLegendreSeries_uniform F hF).tsum_eq

/-- The screenshot formula: the exact Fabius-value coefficients give the
pointwise Legendre expansion of the canonical up function on `[-1,1]`. -/
theorem hasSum_canonical_rvachevLegendreSeries_formula
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦
      ((4 : ℝ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℝ) *
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n + k) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) *
            (Nat.factorial (2 * k) : ℝ) *
            2 ^ (2 * k + 1).choose 2 *
            fabiusReal fabius (((2 : ℝ) ^ (2 * k + 1))⁻¹)) *
        (legendrePolynomial (2 * n)).eval x)) (rvachevUp fabius x) := by
  have hseries := hasSum_rvachevLegendreSeries fabius fabius_spec x hx
  convert hseries using 1
  funext n
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum]

/-- Tsum equality for the screenshot formula. -/
theorem tsum_canonical_rvachevLegendreSeries_formula
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∑' n,
      ((4 : ℝ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℝ) *
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n + k) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) *
            (Nat.factorial (2 * k) : ℝ) *
            2 ^ (2 * k + 1).choose 2 *
            fabiusReal fabius (((2 : ℝ) ^ (2 * k + 1))⁻¹)) *
        (legendrePolynomial (2 * n)).eval x)) = rvachevUp fabius x :=
  (hasSum_canonical_rvachevLegendreSeries_formula x hx).tsum_eq

/-- The screenshot formula converges uniformly on `[-1,1]`. -/
theorem hasSum_canonical_rvachevLegendreSeries_formula_uniform :
    HasSum (fun n ↦
      ((4 : ℝ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℝ) *
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n + k) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) *
            (Nat.factorial (2 * k) : ℝ) *
            2 ^ (2 * k + 1).choose 2 *
            fabiusReal fabius (((2 : ℝ) ^ (2 * k + 1))⁻¹))) •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous)
      (continuousMapOnLegendreInterval
        (rvachevUp fabius) (rvachev_contDiff fabius fabius_spec).continuous) := by
  have hseries := hasSum_rvachevLegendreSeries_uniform fabius fabius_spec
  convert hseries using 1
  funext n
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum]

/-- Uniform tsum equality for the screenshot formula. -/
theorem tsum_canonical_rvachevLegendreSeries_formula_uniform :
    (∑' n,
      ((4 : ℝ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℝ) *
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n + k) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) *
            (Nat.factorial (2 * k) : ℝ) *
            2 ^ (2 * k + 1).choose 2 *
            fabiusReal fabius (((2 : ℝ) ^ (2 * k + 1))⁻¹))) •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous) =
      continuousMapOnLegendreInterval
        (rvachevUp fabius)
        (rvachev_contDiff fabius fabius_spec).continuous :=
  hasSum_canonical_rvachevLegendreSeries_formula_uniform.tsum_eq

end

end Fabius
