import Surreal.Algebra.ArcsinTaylor
import Surreal.Surcomplex.InverseTrigonometricTaylor

/-!
# The actual inverse-sine strong series and inverse-function valuations

The geometric inverse sine has its full central-binomial strong expansion
at every actual infinitesimal. Exact finite remainders and the leading unit
factor supply `trigonometry:eq:smallseries` and the valuation assertions
following `trigonometry:prop:acosendpoint`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- The central-binomial odd-power family is strongly summable at every actual infinitesimal. -/
theorem stronglySummable_arcsinTaylor (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) * x ^ (2 * n + 1)) := by
  have hs := SignSequence.stronglySummable_coeff_mul_powers x hx
    (fun n => (Analytic.taylorSeries Real.arcsin 0).coeff n)
  simpa only [Analytic.coeff_taylorSeries_arcsin_odd] using
    hs.comp_injective (fun n : ℕ => 2 * n + 1) (by intro a b h; dsimp at h; omega)

/-- The full inverse-sine expansion is an actual strong sum with explicit central-binomial terms. -/
theorem arcsinFunction_eq_strongSum (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    arcsinFunction x = SignSequence.strongSum (fun n : ℕ =>
      SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) * x ^ (2 * n + 1))
      (stronglySummable_arcsinTaylor x hx) := by
  have hs := SignSequence.stronglySummable_coeff_mul_powers x hx
    (fun n => (Analytic.taylorSeries Real.arcsin 0).coeff n)
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k + 1) →
      SignSequence.ofReal ((Analytic.taylorSeries Real.arcsin 0).coeff n) * x ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [Analytic.coeff_taylorSeries_arcsin_even, map_zero, zero_mul]
    · exact (hn ⟨k, rfl⟩).elim
  have he := SignSequence.strongSum_comp_injective hs (fun n : ℕ => 2 * n + 1)
    (by intro a b h; dsimp at h; omega) hz
  rw [arcsinFunction_eq_powerSeries x hx, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simpa only [Analytic.coeff_taylorSeries_arcsin_odd] using he.symm

/-- The inverse-sine expansion through degree seven has an exact finite ninth-order remainder. -/
theorem arcsinFunction_expansion (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 35 / 1152 ∧
      arcsinFunction x = x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + 5 * x ^ 7 / 112 + x ^ 9 * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder x hx
    (Analytic.taylorSeries Real.arcsin 0) 9
  rw [← arcsinFunction_eq_powerSeries x hx] at he
  simp_rw [Analytic.coeff_taylorSeries_arcsin_zero] at hr he
  norm_num [Finset.sum_range_succ, Nat.centralBinom, Nat.choose_succ_succ, map_div₀, map_ofNat] at hr he
  refine ⟨R, hR, hr, ?_⟩
  linear_combination he

/-- The inverse-sine leading factor is finite with standard part one. -/
theorem arcsinFunction_leading_factor (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 ∧
      arcsinFunction x = x * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder x hx
    (Analytic.taylorSeries Real.arcsin 0) 1
  rw [← arcsinFunction_eq_powerSeries x hx] at he
  rw [Analytic.coeff_taylorSeries_arcsin_one] at hr
  refine ⟨R, hR, hr, ?_⟩
  simpa only [Finset.sum_range_one, Analytic.coeff_taylorSeries, iteratedDeriv_zero,
    Real.arcsin_zero, zero_div, map_zero, zero_mul, zero_add, pow_one] using he

/-- Inverse tangent has the same finite leading factor property. -/
theorem arctanFunction_leading_factor (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 ∧
      arctanFunction x = x * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder x hx
    (Analytic.taylorSeries Real.arctan 0) 1
  rw [← arctanFunction_eq_powerSeries x hx] at he
  rw [Analytic.coeff_taylorSeries_arctan_one] at hr
  refine ⟨R, hR, hr, ?_⟩
  simpa only [Finset.sum_range_one, Analytic.coeff_taylorSeries, iteratedDeriv_zero,
    Real.arctan_zero, zero_div, map_zero, zero_mul, zero_add, pow_one] using he

/-- Inverse sine preserves the exact valuation at zero, including the zero input. -/
theorem valuation_arcsinFunction_of_isInfinitesimal (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.valuation (arcsinFunction x) = SignSequence.valuation x := by
  obtain ⟨R, hR, hr, he⟩ := arcsinFunction_leading_factor x hx
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hR).mpr
    (by rw [hr]; norm_num)
  rw [he, SignSequence.valuation_mul, hv, add_zero]

/-- Inverse tangent preserves the exact valuation at zero, including the zero input. -/
theorem valuation_arctanFunction_of_isInfinitesimal (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.valuation (arctanFunction x) = SignSequence.valuation x := by
  obtain ⟨R, hR, hr, he⟩ := arctanFunction_leading_factor x hx
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hR).mpr
    (by rw [hr]; norm_num)
  rw [he, SignSequence.valuation_mul, hv, add_zero]

/-- An infinitesimal input has infinitesimal inverse sine. -/
theorem infinitesimal_arcsinFunction (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.IsInfinitesimal (arcsinFunction x) := by
  rw [arcsinFunction_eq_powerSeries x hx]
  apply (SignSequence.isInfinitesimal_powerSeriesEvaluation_iff x hx _).mpr
  simp

/-- Inverse sine is algebraically equivalent to its nonzero infinitesimal input. -/
theorem infinitesimal_arcsinFunction_div_sub_one (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) (hne : x ≠ 0) :
    SignSequence.IsInfinitesimal (arcsinFunction x / x - 1) := by
  obtain ⟨R, hR, hr, he⟩ := arcsinFunction_leading_factor x hx
  rw [he, mul_div_cancel_left₀ _ hne]
  simpa only [hr, map_one] using SignSequence.infinitesimal_sub_standardPart hR

/-- Inverse tangent is algebraically equivalent to its nonzero infinitesimal input. -/
theorem infinitesimal_arctanFunction_div_sub_one (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) (hne : x ≠ 0) :
    SignSequence.IsInfinitesimal (arctanFunction x / x - 1) := by
  obtain ⟨R, hR, hr, he⟩ := arctanFunction_leading_factor x hx
  rw [he, mul_div_cancel_left₀ _ hne]
  simpa only [hr, map_one] using SignSequence.infinitesimal_sub_standardPart hR

end Surreal.Surcomplex
