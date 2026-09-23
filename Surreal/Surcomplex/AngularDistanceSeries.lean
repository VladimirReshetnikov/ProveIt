import Surreal.Surcomplex.AngularDistance
import Surreal.Surcomplex.TrigonometricLeading

/-!
# Full normalized chord and cosine-defect series

The normalized factors in `trigonometry:eq:chordseries` are explicit formal
power series evaluated by actual strong sums. Their coefficients, constant
terms and exact finite remainders retain the full infinitesimal scale.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The normalized chord germ `2*sin(X/2)/X`, with its removable value at zero. -/
def chordNormalizedSeries : PowerSeries ℝ :=
  PowerSeries.rescale (1 / 2)
    (PowerSeries.mk (fun n => (Analytic.taylorSeries Real.sin 0).coeff (n + 1)))

/-- The normalized cosine-defect germ `2*(1-cos(X))/X^2`. -/
def cosineDefectNormalizedSeries : PowerSeries ℝ :=
  PowerSeries.C (-2) *
    PowerSeries.mk (fun n => (Analytic.taylorSeries Real.cos 0).coeff (n + 2))

theorem coeff_chordNormalizedSeries (n : ℕ) :
    PowerSeries.coeff n chordNormalizedSeries =
      (1 / 2 : ℝ) ^ n * (Analytic.taylorSeries Real.sin 0).coeff (n + 1) := by
  simp only [chordNormalizedSeries, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]

theorem coeff_cosineDefectNormalizedSeries (n : ℕ) :
    PowerSeries.coeff n cosineDefectNormalizedSeries =
      -2 * (Analytic.taylorSeries Real.cos 0).coeff (n + 2) := by
  simp only [cosineDefectNormalizedSeries, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

/-- Every even normalized chord coefficient is the expected scaled factorial coefficient. -/
theorem coeff_chordNormalizedSeries_even (n : ℕ) :
    PowerSeries.coeff (2 * n) chordNormalizedSeries =
      (-1 : ℝ) ^ n / (2 ^ (2 * n) * (2 * n + 1).factorial) := by
  rw [coeff_chordNormalizedSeries, Analytic.coeff_taylorSeries_sin_zero]
  have ho : ¬ Even (2 * n + 1) := by simp
  rw [if_neg ho]
  rw [show (2 * n + 1) / 2 = n by omega, div_pow, one_pow]
  ring

@[simp] theorem coeff_chordNormalizedSeries_odd (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) chordNormalizedSeries = 0 := by
  rw [coeff_chordNormalizedSeries, show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
    Analytic.coeff_taylorSeries_sin_zero]
  simp

/-- Every even normalized cosine-defect coefficient is explicit. -/
theorem coeff_cosineDefectNormalizedSeries_even (n : ℕ) :
    PowerSeries.coeff (2 * n) cosineDefectNormalizedSeries =
      2 * (-1 : ℝ) ^ n / (2 * n + 2).factorial := by
  rw [coeff_cosineDefectNormalizedSeries, Analytic.coeff_taylorSeries_cos_zero]
  have he : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  rw [if_pos he, show (2 * n + 2) / 2 = n + 1 by omega, pow_succ]
  ring

@[simp] theorem coeff_cosineDefectNormalizedSeries_odd (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) cosineDefectNormalizedSeries = 0 := by
  rw [coeff_cosineDefectNormalizedSeries, Analytic.coeff_taylorSeries_cos_zero]
  have he : ¬ Even (2 * n + 1 + 2) := by
    rw [show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega]
    simp
  rw [if_neg he, mul_zero]

private theorem infinitesimal_half_angle (θ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal θ.val) :
    SignSequence.IsInfinitesimal (finiteHalf θ).val := by
  apply SignSequence.infinitesimal_of_abs_le (y := θ.val) _ hi
  rw [val_finiteHalf, abs_div, abs_of_pos (by norm_num : (0 : SignSequence.{u}) < 2)]
  have h := abs_nonneg θ.val
  linarith only [h]

private theorem evaluation_rescale_half (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) (hh : SignSequence.IsInfinitesimal (x / 2))
    (f : PowerSeries ℝ) :
    SignSequence.powerSeriesEvaluation x hx (PowerSeries.rescale (1 / 2) f) =
      SignSequence.powerSeriesEvaluation (x / 2) hh f := by
  rw [SignSequence.powerSeriesEvaluation_eq_strongSum,
    SignSequence.powerSeriesEvaluation_eq_strongSum]
  have he : (fun n : ℕ =>
      SignSequence.ofReal ((PowerSeries.rescale (1 / 2) f).coeff n) * x ^ n) =
      (fun n : ℕ => SignSequence.ofReal (f.coeff n) * (x / 2) ^ n) := by
    funext n
    simp only [PowerSeries.coeff_rescale, map_mul, map_pow, map_div₀, map_one, map_ofNat, div_pow]
    ring
  simp only [he]

private theorem two_eval_sin_half_eq (x : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal x) (hh : SignSequence.IsInfinitesimal (x / 2)) :
    2 * SignSequence.powerSeriesEvaluation (x / 2) hh (Analytic.taylorSeries Real.sin 0) =
      x * SignSequence.powerSeriesEvaluation x hi chordNormalizedSeries := by
  have ht : PowerSeries.trunc 1 (Analytic.taylorSeries Real.sin 0) = 0 := by
    norm_num [PowerSeries.trunc_succ, Analytic.coeff_taylorSeries_sin_zero]
  have hf := PowerSeries.eq_X_pow_mul_shift_add_trunc 1 (Analytic.taylorSeries Real.sin 0)
  rw [ht, Polynomial.coe_zero, add_zero, pow_one] at hf
  have he := congrArg (SignSequence.powerSeriesEvaluation (x / 2) hh) hf
  simp only [map_mul, SignSequence.powerSeriesEvaluation_X] at he
  rw [he, chordNormalizedSeries, evaluation_rescale_half x hi hh]
  ring

/-- The half-angle sine has the normalized chord factor at every infinitesimal angle. -/
theorem two_finiteSin_half_eq_normalizedSeries (θ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal θ.val) :
    2 * finiteSin (finiteHalf θ) = θ.val *
      SignSequence.powerSeriesEvaluation θ.val hi chordNormalizedSeries := by
  have hh₀ := infinitesimal_half_angle θ hi
  have hh : SignSequence.IsInfinitesimal (θ.val / 2) := by
    simpa only [val_finiteHalf] using hh₀
  calc
    2 * finiteSin (finiteHalf θ) = 2 * SignSequence.powerSeriesEvaluation (θ.val / 2) hh
        (Analytic.taylorSeries Real.sin 0) := by
      congr 1
      simpa only [val_finiteHalf] using
        finiteSin_eq_powerSeries_of_isInfinitesimal (finiteHalf θ) hh₀
    _ = _ := two_eval_sin_half_eq θ.val hi hh

/-- The cosine defect has its normalized formal factor at every infinitesimal angle. -/
theorem one_sub_finiteCos_eq_normalizedSeries (θ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal θ.val) :
    1 - finiteCos θ = θ.val ^ 2 / 2 *
      SignSequence.powerSeriesEvaluation θ.val hi cosineDefectNormalizedSeries := by
  have ht : PowerSeries.trunc 2 (Analytic.taylorSeries Real.cos 0) = 1 := by
    norm_num [PowerSeries.trunc_succ, Analytic.coeff_taylorSeries_cos_zero]
  have hf := PowerSeries.eq_X_pow_mul_shift_add_trunc 2 (Analytic.taylorSeries Real.cos 0)
  rw [ht, Polynomial.coe_one] at hf
  have he := congrArg (SignSequence.powerSeriesEvaluation θ.val hi) hf
  simp only [map_add, map_mul, map_pow, map_one, SignSequence.powerSeriesEvaluation_X] at he
  rw [finiteCos_eq_powerSeries_of_isInfinitesimal θ hi, he,
    cosineDefectNormalizedSeries, map_mul, SignSequence.powerSeriesEvaluation_C]
  norm_num only [map_neg, map_ofNat]
  ring

/-- The chord's exact normalized factor is the full formal series evaluated at the distance. -/
theorem modulus_unitCircle_sub_eq_normalizedSeries (z w : UnitCircle.{u})
    (hi : SignSequence.IsInfinitesimal (angularDistance z w)) :
    modulus (z.val - w.val) = angularDistance z w *
      SignSequence.powerSeriesEvaluation (angularDistance z w) hi chordNormalizedSeries := by
  rw [modulus_unitCircle_sub_eq_two_sin, two_finiteSin_half_eq_normalizedSeries _ hi]
  rfl

/-- The unit-circle cosine defect has its exact normalized formal factor. -/
theorem unitCircle_cosine_defect_eq_normalizedSeries (z w : UnitCircle.{u})
    (hi : SignSequence.IsInfinitesimal (angularDistance z w)) :
    1 - finiteCos (unitCircleAngle (z⁻¹ * w)) = angularDistance z w ^ 2 / 2 *
      SignSequence.powerSeriesEvaluation (angularDistance z w) hi cosineDefectNormalizedSeries :=
  one_sub_finiteCos_eq_normalizedSeries _ hi

/-- Both normalized factors have constant term one. -/
theorem normalizedAngularSeries_constantCoeffs :
    PowerSeries.constantCoeff chordNormalizedSeries = 1 ∧
      PowerSeries.constantCoeff cosineDefectNormalizedSeries = 1 := by
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_chordNormalizedSeries, coeff_cosineDefectNormalizedSeries]
  norm_num [Analytic.coeff_taylorSeries_sin_zero, Analytic.coeff_taylorSeries_cos_zero]

/-- The normalized chord identity is literally a strongly summable coefficient family. -/
theorem modulus_unitCircle_sub_eq_strongSeries (z w : UnitCircle.{u})
    (hi : SignSequence.IsInfinitesimal (angularDistance z w)) :
    modulus (z.val - w.val) = angularDistance z w *
      SignSequence.strongSum
        (fun n : ℕ => SignSequence.ofReal (chordNormalizedSeries.coeff n) * angularDistance z w ^ n)
        (SignSequence.stronglySummable_coeff_mul_powers (angularDistance z w) hi _) := by
  rw [modulus_unitCircle_sub_eq_normalizedSeries z w hi,
    SignSequence.powerSeriesEvaluation_eq_strongSum]

/-- The normalized cosine defect likewise has a full actual strong-sum formula. -/
theorem unitCircle_cosine_defect_eq_strongSeries (z w : UnitCircle.{u})
    (hi : SignSequence.IsInfinitesimal (angularDistance z w)) :
    1 - finiteCos (unitCircleAngle (z⁻¹ * w)) = angularDistance z w ^ 2 / 2 *
      SignSequence.strongSum
        (fun n : ℕ => SignSequence.ofReal (cosineDefectNormalizedSeries.coeff n) *
          angularDistance z w ^ n)
        (SignSequence.stronglySummable_coeff_mul_powers (angularDistance z w) hi _) := by
  rw [unitCircle_cosine_defect_eq_normalizedSeries z w hi,
    SignSequence.powerSeriesEvaluation_eq_strongSum]

/-- The two strong normalized factors are finite and both have standard part one. -/
theorem normalizedAngularSeries_finite_residue (d : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal d) :
    SignSequence.IsFinite (SignSequence.powerSeriesEvaluation d hi chordNormalizedSeries) ∧
      SignSequence.standardPart (SignSequence.powerSeriesEvaluation d hi chordNormalizedSeries) = 1 ∧
      SignSequence.IsFinite (SignSequence.powerSeriesEvaluation d hi cosineDefectNormalizedSeries) ∧
      SignSequence.standardPart
        (SignSequence.powerSeriesEvaluation d hi cosineDefectNormalizedSeries) = 1 := by
  exact ⟨SignSequence.isFinite_powerSeriesEvaluation d hi _,
    (SignSequence.standardPart_powerSeriesEvaluation d hi _).trans
      normalizedAngularSeries_constantCoeffs.1,
    SignSequence.isFinite_powerSeriesEvaluation d hi _,
    (SignSequence.standardPart_powerSeriesEvaluation d hi _).trans
      normalizedAngularSeries_constantCoeffs.2⟩

/-- The displayed chord series has an exact finite normalized sixth-order remainder. -/
theorem modulus_unitCircle_sub_expansion (z w : UnitCircle.{u})
    (hi : SignSequence.IsInfinitesimal (angularDistance z w)) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧
      SignSequence.standardPart R = -1 / 322560 ∧
      modulus (z.val - w.val) = angularDistance z w *
        (1 - angularDistance z w ^ 2 / 24 + angularDistance z w ^ 4 / 1920 +
          angularDistance z w ^ 6 * R) := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder
    (angularDistance z w) hi chordNormalizedSeries 6
  norm_num [coeff_chordNormalizedSeries, Finset.sum_range_succ,
    Analytic.coeff_taylorSeries_sin_zero, map_div₀, map_neg, map_ofNat] at hr he
  refine ⟨R, hR, by simpa only [neg_div] using hr, ?_⟩
  rw [modulus_unitCircle_sub_eq_normalizedSeries z w hi, he]
  ring

/-- The displayed cosine-defect series has an exact finite normalized sixth-order remainder. -/
theorem unitCircle_cosine_defect_expansion (z w : UnitCircle.{u})
    (hi : SignSequence.IsInfinitesimal (angularDistance z w)) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧
      SignSequence.standardPart R = -1 / 20160 ∧
      1 - finiteCos (unitCircleAngle (z⁻¹ * w)) = angularDistance z w ^ 2 / 2 *
        (1 - angularDistance z w ^ 2 / 12 + angularDistance z w ^ 4 / 360 +
          angularDistance z w ^ 6 * R) := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder
    (angularDistance z w) hi cosineDefectNormalizedSeries 6
  norm_num [coeff_cosineDefectNormalizedSeries, Finset.sum_range_succ,
    Analytic.coeff_taylorSeries_cos_zero, map_div₀, map_neg, map_ofNat] at hr he
  refine ⟨R, hR, by simpa only [neg_div] using hr, ?_⟩
  rw [unitCircle_cosine_defect_eq_normalizedSeries z w hi, he]
  ring

end
end Surreal.Surcomplex
