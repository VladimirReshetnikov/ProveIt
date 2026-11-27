import GRHArticle.ProgressionFree.PolynomialReplacementCoefficient
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The finite geometric product in the deficit replacement

Each index with degree `d > 0` contributes a geometric series supported on
multiples of `d`. This defines the product over smooth primes by specializing the
finite index set to those primes and taking the usual polynomial degree.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- The geometric series with a term at each multiple of the degree. -/
def degreeGeometricSeries (d : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk (fun n ↦ if d ∣ n then 1 else 0)

/-- The formal geometric product associated to a finite family of degrees. -/
noncomputable def smoothDegreeCountingSeries {ι : Type*} (S : Finset ι)
    (degree : ι → ℕ) : PowerSeries ℕ :=
  ∏ i ∈ S, degreeGeometricSeries (degree i)

private theorem weighted_series_summable_mul {z : ℝ} (hz : 0 ≤ z) {A B : PowerSeries ℕ}
    (hA : Summable (fun n ↦ (PowerSeries.coeff (R := ℕ) n A : ℝ) * z ^ n))
    (hB : Summable (fun n ↦ (PowerSeries.coeff (R := ℕ) n B : ℝ) * z ^ n)) :
    Summable (fun n ↦ (PowerSeries.coeff (R := ℕ) n (A * B) : ℝ) * z ^ n) := by
  have nonneg (C : PowerSeries ℕ) (n : ℕ) : 0 ≤ (PowerSeries.coeff (R := ℕ) n C : ℝ) * z ^ n :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)
  have hAn : Summable (fun n ↦ ‖(PowerSeries.coeff (R := ℕ) n A : ℝ) * z ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (nonneg A _)] using hA
  have hBn : Summable (fun n ↦ ‖(PowerSeries.coeff (R := ℕ) n B : ℝ) * z ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (nonneg B _)] using hB
  have hweight (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        ((PowerSeries.coeff (R := ℕ) k A : ℝ) * z ^ k) *
          ((PowerSeries.coeff (R := ℕ) (n - k) B : ℝ) * z ^ (n - k))) =
        (PowerSeries.coeff (R := ℕ) n (A * B) : ℝ) * z ^ n := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : z ^ k * z ^ (n - k) = z ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]
    rw [← hpow]
    ring
  simpa only [hweight] using (summable_norm_sum_mul_range_of_summable_norm hAn hBn).of_norm

theorem smoothDegreeCountingSeries_constantCoeff {ι : Type*} (S : Finset ι)
    (degree : ι → ℕ) : PowerSeries.coeff 0 (smoothDegreeCountingSeries S degree) = 1 := by
  simp [smoothDegreeCountingSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    degreeGeometricSeries, PowerSeries.constantCoeff_mk]

/-- Finite products of geometric degree series converge at every real `0 ≤ z < 1`. -/
theorem summable_smoothDegreeCountingSeries {ι : Type*} (S : Finset ι) (degree : ι → ℕ)
    {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    Summable (fun n ↦ (PowerSeries.coeff (R := ℕ) n (smoothDegreeCountingSeries S degree) : ℝ) * z ^ n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hfun : (fun n ↦ (PowerSeries.coeff (R := ℕ) n (smoothDegreeCountingSeries ∅ degree) : ℝ) *
        z ^ n) = fun n ↦ if n = 0 then 1 else 0 := by
      funext n
      by_cases hn : n = 0 <;> simp [smoothDegreeCountingSeries, hn]
    rw [hfun]
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hne : n ≠ 0 := by simpa using hn
    simp [hne]
  | @insert i S hi ih =>
    have hgeom : Summable (fun n ↦ (PowerSeries.coeff (R := ℕ) n (degreeGeometricSeries (degree i)) : ℝ) *
        z ^ n) := by
      apply (summable_geometric_of_lt_one hz₀ hz₁).of_nonneg_of_le
      · intro n
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz₀ _)
      · intro n
        by_cases h : degree i ∣ n <;>
          simp [degreeGeometricSeries, h, pow_nonneg hz₀ n]
    simpa only [smoothDegreeCountingSeries, Finset.prod_insert hi] using
      weighted_series_summable_mul hz₀ hgeom ih

set_option maxHeartbeats 1000000 in
/-- The product of the geometric degree series and the explicit signed replacement
series has a positive integer coefficient. -/
theorem smoothDegreeCountingSeries_exists_positive_coefficient {ι : Type*} (S : Finset ι)
    (degree : ι → ℕ) :
    ∃ R, 1 ≤ PowerSeries.coeff R
      (PowerSeries.map (Nat.castRingHom ℤ) (smoothDegreeCountingSeries S degree) *
        PowerSeries.mk polynomialDeficitDifference) := by
  have hzero : 0 < PowerSeries.coeff 0 (smoothDegreeCountingSeries S degree) := by
    rw [smoothDegreeCountingSeries_constantCoeff]
    decide
  obtain ⟨R, hR⟩ := polynomialDeficitDifference_exists_positive_convolution hzero
    (summable_smoothDegreeCountingSeries S degree (by norm_num : (0 : ℝ) ≤ 127 / 128)
      (by norm_num : (127 : ℝ) / 128 < 1))
  refine ⟨R, ?_⟩
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [PowerSeries.coeff_map, PowerSeries.coeff_mk, Nat.coe_castRingHom] using hR

end GRHArticle.ProgressionFree
