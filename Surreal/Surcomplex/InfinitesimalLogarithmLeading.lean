import Surreal.Surcomplex.ExpLog
import Surreal.Surcomplex.PowerSeriesLeading
import Surreal.Surcomplex.PowerSeriesTruncation
import Surreal.Foundations.SignSequenceFiniteUnits

/-!
# Leading data and finite remainders for the local surcomplex logarithm

The strong logarithm preserves the valuation and leading coefficient of
every actual infinitesimal. Its imaginary coordinate has no smaller
valuation, with equality if the first complex coefficient has nonzero
imaginary part. These give the series and valuation prerequisites for
`trigonometry:cor:directionstability`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

private theorem logSeries_ne_zero : PowerSeries.log ℂ ≠ 0 := by
  intro h
  have he := congrArg (PowerSeries.coeff 1) h
  simp at he

/-- The logarithm through degree two has an exact finite cubic remainder of residue one third. -/
theorem infLog_expansion (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = 1 / 3 ∧
      infLog η hη = η - η ^ 2 / 2 + η ^ 3 * R := by
  obtain ⟨R, hR, hr, he⟩ := exists_finite_powerSeries_remainder η hη (PowerSeries.log ℂ) 3
  norm_num [PowerSeries.coeff_log, Finset.sum_range_succ, map_div₀, map_ofNat] at hr he
  refine ⟨R, hR, hr, ?_⟩
  change powerSeriesEvaluation η hη (PowerSeries.log ℂ) = _
  linear_combination he

/-- The strong logarithm preserves valuation, including at zero. -/
theorem valuation_infLog (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    valuation (infLog η hη) = valuation η := by
  simpa only [infLog, PowerSeries.order_log, ENat.toNat_one, one_nsmul] using
    valuation_powerSeriesEvaluation η hη (PowerSeries.log ℂ) logSeries_ne_zero

/-- The strong logarithm preserves the ordinary complex leading coefficient. -/
theorem leadingCoeff_infLog (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    leadingCoeff (infLog η hη) = leadingCoeff η := by
  simpa only [infLog, PowerSeries.order_log, ENat.toNat_one, PowerSeries.coeff_one_log,
    pow_one, one_mul] using
    leadingCoeff_powerSeriesEvaluation η hη (PowerSeries.log ℂ) logSeries_ne_zero

/-- A nonzero imaginary leading coefficient makes the imaginary coordinate retain full valuation. -/
theorem valuation_im_eq_of_leadingCoeff_im_ne_zero (z : Surcomplex.{u})
    (hz : (leadingCoeff z).im ≠ 0) : SignSequence.valuation z.im = valuation z := by
  have hne : z ≠ 0 := by
    intro h
    simp only [h, leadingCoeff_zero, Complex.zero_im, ne_self_iff_false] at hz
  have hv : SignSequence.valuation (normalized z).im = 0 :=
    (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero (finite_normalized z).2).mpr hz
  have he := congrArg (fun w : Surcomplex.{u} => w.im) (monomial_mul_normalized z)
  simp only [tMonomial, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] at he
  rw [← he, SignSequence.valuation_mul, hv, add_zero, SignSequence.valuation_tMonomial,
    valuation_of_ne_zero hne]
  rfl

/-- Taking imaginary parts of a local logarithm cannot lower the infinitesimal's valuation. -/
theorem valuation_im_infLog_ge (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    valuation η ≤ SignSequence.valuation (infLog η hη).im := by
  rw [← valuation_infLog η hη, valuation_eq_min_coordinates]
  exact min_le_right _ _

/-- The imaginary logarithm retains full valuation when the leading coefficient is not real. -/
theorem valuation_im_infLog_eq_of_leadingCoeff_im_ne_zero (η : Surcomplex.{u})
    (hη : IsInfinitesimal η) (him : (leadingCoeff η).im ≠ 0) :
    SignSequence.valuation (infLog η hη).im = valuation η := by
  rw [valuation_im_eq_of_leadingCoeff_im_ne_zero _ (by rwa [leadingCoeff_infLog]),
    valuation_infLog]

/-- The imaginary logarithm has a cubic remainder bounded by a finite modulus multiplier. -/
theorem infLog_im_expansion (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = 1 / 3 ∧
      (infLog η hη).im = η.im - (η ^ 2).im / 2 + (η ^ 3 * R).im ∧
      |(η ^ 3 * R).im| ≤ modulus η ^ 3 * modulus R := by
  obtain ⟨R, hR, hr, he⟩ := infLog_expansion η hη
  refine ⟨R, hR, hr, ?_, ?_⟩
  · have htwo : (2 : Surcomplex.{u})⁻¹ = ofReal ((2 : SignSequence.{u})⁻¹) := by
      rw [map_inv₀, map_ofNat]
    have him := congrArg (fun w : Surcomplex.{u} => w.im) he
    have hd : (η ^ 2 / 2).im = (η ^ 2).im / 2 := by
      rw [div_eq_mul_inv, htwo, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]
      rfl
    change (infLog η hη).im = η.im - (η ^ 2 / 2).im + (η ^ 3 * R).im at him
    rwa [hd] at him
  · have hm := abs_im_le_modulus (η ^ 3 * R)
    rw [modulus_mul] at hm
    change |(η ^ 3 * R).im| ≤ modulusMonoidWithZeroHom (η ^ 3) * modulus R at hm
    rw [map_pow] at hm
    exact hm

/-- The quadratic imaginary-logarithm error is bounded by the cubic modulus times a finite factor. -/
theorem infLog_im_remainder_bound (η : Surcomplex.{u}) (hη : IsInfinitesimal η) :
    ∃ B : SignSequence.{u}, SignSequence.IsFinite B ∧ 0 ≤ B ∧
      |(infLog η hη).im - (η.im - (η ^ 2).im / 2)| ≤ modulus η ^ 3 * B := by
  obtain ⟨R, hR, _, he, hb⟩ := infLog_im_expansion η hη
  refine ⟨modulus R, (isFinite_iff_modulus R).mp hR, modulus_nonneg R, ?_⟩
  calc
    _ = |(η ^ 3 * R).im| := by congr 1; rw [he]; ring
    _ ≤ _ := hb

end Surreal.Surcomplex
