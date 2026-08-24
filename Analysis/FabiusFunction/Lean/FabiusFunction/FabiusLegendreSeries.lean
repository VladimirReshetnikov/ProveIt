import FabiusFunction.FabiusLegendreCoefficients
import FabiusFunction.LegendreSeriesConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Fourier--Legendre series of Rvachev's up function

This file combines the exact coefficient evaluation with the analytic
convergence theorem.  The expansion is understood on the natural Legendre
interval `[-1, 1]`; convergence there is absolute and uniform, and therefore
also pointwise at both endpoints.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Interval Polynomial
open Set MeasureTheory

namespace Fabius

noncomputable section

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

/-! ## Removing the zero odd subsequence -/

/-- If every odd term of a real series is zero, its sum is already the sum of
the even subsequence. -/
private theorem hasSum_even_of_odd_eq_zero
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {a : E}
    (h : HasSum f a) (hodd : ∀ n, f (2 * n + 1) = 0) :
    HasSum (fun n ↦ f (2 * n)) a := by
  have heSummable : Summable (fun n ↦ f (2 * n)) :=
    h.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have he := heSummable.hasSum
  have ho : HasSum (fun n ↦ f (2 * n + 1)) 0 := by
    convert hasSum_zero
    exact hodd _
  have hcombined : HasSum f ((∑' n, f (2 * n)) + 0) := he.even_add_odd ho
  have hsum : (∑' n, f (2 * n)) = a := by
    simpa using HasSum.unique hcombined h
  rwa [hsum] at he

/-! ## Specialization to Rvachev's up function -/

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

private theorem hasSum_rvachevFullLegendreSeries_of_properties
    (F : BoundedFabius) (hF : IsFabius F)
    (hpEigen : ∀ n x,
      legendreSturmLiouville
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      |(legendrePolynomial n).eval x| ≤ 1)
    (hpNorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (legendrePolynomial n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ)))
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦
      rvachevFullLegendreCoefficient F n * (legendrePolynomial n).eval x)
      (rvachevUp F x) := by
  have horthogonal : ∀ m n, m ≠ n →
      (∫ y in (-1 : ℝ)..1,
        (legendrePolynomial m).eval y * (legendrePolynomial n).eval y) = 0 := by
    intro m n hmn
    exact integral_eigenpolynomial_mul_eq_zero_of_ne legendrePolynomial
      legendrePolynomial_contDiff_infty hpEigen hmn
  simpa only [legendreSeriesCoefficientOf_rvachevUp] using
    hasSum_legendrePolynomialSeries_eq
      (rvachevUp F) (rvachev_contDiff F hF) legendrePolynomial
      degree_legendrePolynomial legendrePolynomial_contDiff_infty hpEigen hpBound
      horthogonal hpNorm x hx

private theorem hasSum_rvachevFullLegendreSeries_uniform_of_properties
    (F : BoundedFabius) (hF : IsFabius F)
    (hpEigen : ∀ n x,
      legendreSturmLiouville
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      |(legendrePolynomial n).eval x| ≤ 1)
    (hpNorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (legendrePolynomial n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ))) :
    HasSum (fun n ↦
      rvachevFullLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial n).eval x)
          (legendrePolynomial_contDiff n).continuous)
      (continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous) := by
  have horthogonal : ∀ m n, m ≠ n →
      (∫ y in (-1 : ℝ)..1,
        (legendrePolynomial m).eval y * (legendrePolynomial n).eval y) = 0 := by
    intro m n hmn
    exact integral_eigenpolynomial_mul_eq_zero_of_ne legendrePolynomial
      legendrePolynomial_contDiff_infty hpEigen hmn
  simpa only [legendreSeriesCoefficientOf_rvachevUp] using
    hasSum_legendrePolynomialSeries_eq_uniform
      (rvachevUp F) (rvachev_contDiff F hF) legendrePolynomial
      degree_legendrePolynomial legendrePolynomial_contDiff_infty hpEigen hpBound
      horthogonal hpNorm

private theorem hasSum_rvachevEvenLegendreSeries_of_properties
    (F : BoundedFabius) (hF : IsFabius F)
    (hpEigen : ∀ n x,
      legendreSturmLiouville
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      |(legendrePolynomial n).eval x| ≤ 1)
    (hpNorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (legendrePolynomial n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ)))
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦
      rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x) (rvachevUp F x) := by
  have hfull := hasSum_rvachevFullLegendreSeries_of_properties
    F hF hpEigen hpBound hpNorm x hx
  have heven := hasSum_even_of_odd_eq_zero hfull (fun n ↦ by
    rw [rvachevFullLegendreCoefficient_odd_eq_zero F hF n, zero_mul])
  simpa only [rvachevFullLegendreCoefficient_even_eq] using heven

private theorem hasSum_rvachevEvenLegendreSeries_uniform_of_properties
    (F : BoundedFabius) (hF : IsFabius F)
    (hpEigen : ∀ n x,
      legendreSturmLiouville
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      |(legendrePolynomial n).eval x| ≤ 1)
    (hpNorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (legendrePolynomial n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ))) :
    HasSum (fun n ↦
      rvachevLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ ↦ (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous)
      (continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous) := by
  have hfull := hasSum_rvachevFullLegendreSeries_uniform_of_properties
    F hF hpEigen hpBound hpNorm
  have heven := hasSum_even_of_odd_eq_zero hfull (fun n ↦ by
    rw [rvachevFullLegendreCoefficient_odd_eq_zero F hF n, zero_smul])
  simpa only [rvachevFullLegendreCoefficient_even_eq] using heven

private theorem hasSum_canonical_rvachevLegendreSeries_formula_of_properties
    (hpEigen : ∀ n x,
      legendreSturmLiouville
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      |(legendrePolynomial n).eval x| ≤ 1)
    (hpNorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (legendrePolynomial n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ)))
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
  have hseries := hasSum_rvachevEvenLegendreSeries_of_properties
    fabius fabius_spec hpEigen hpBound hpNorm x hx
  convert hseries using 1
  funext n
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum]

private theorem hasSum_canonical_rvachevLegendreSeries_formula_uniform_of_properties
    (hpEigen : ∀ n x,
      legendreSturmLiouville
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (legendrePolynomial n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      |(legendrePolynomial n).eval x| ≤ 1)
    (hpNorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (legendrePolynomial n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ))) :
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
  have hseries := hasSum_rvachevEvenLegendreSeries_uniform_of_properties
    fabius fabius_spec hpEigen hpBound hpNorm
  convert hseries using 1
  funext n
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum]

end

end Fabius
