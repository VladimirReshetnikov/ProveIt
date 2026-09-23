import Surreal.Surcomplex.DirectionNormalization
import Surreal.Surcomplex.InfinitesimalLogarithmLeading

/-!
# Stability of direction under a relative infinitesimal perturbation

For an arbitrary nonzero actual surcomplex number, a relatively
infinitesimal perturbation has an infinitesimal geometric direction
change. Identify that angle with the imaginary strong logarithm, then
prove its quadratic expansion, cubic error bound, and exact leading
valuation criterion. This proves `trigonometry:cor:directionstability`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A relatively infinitesimal perturbation cannot annihilate a nonzero element. -/
theorem add_ne_zero_of_relative_infinitesimal (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) : z + h ≠ 0 := by
  have he : 1 + h / z ≠ 0 := by
    simpa only [infExp_infLog] using
      infExp_ne_zero (infLog (h / z) hi) (infinitesimal_infLog (h / z) hi)
  have hf : z + h = z * (1 + h / z) := by field_simp
  rw [hf]
  exact mul_ne_zero hz he

private theorem relative_add_units_sub_one (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hzh : z + h ≠ 0) :
    ((Units.mk0 (z + h) hzh / Units.mk0 z hz : Surcomplex.{u}ˣ) : Surcomplex.{u}) - 1 =
      h / z := by
  simp only [Units.val_div_eq_div_val, Units.val_mk0]
  field_simp
  ring

/-- The canonical infinitesimal angle between the directions of `z` and `z + h`. -/
def directionChange (z h : Surcomplex.{u}) (hz : z ≠ 0) (hi : IsInfinitesimal (h / z)) :
    SignSequence.infinitesimalAddSubgroup.{u} :=
  localAngle (unitDirection (Units.mk0 z hz))
    (unitDirection (Units.mk0 (z + h) (add_ne_zero_of_relative_infinitesimal z h hz hi)))

/-- Relatively infinitesimal perturbations preserve the ordinary direction. -/
theorem direction_standardPart_eq (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) :
    standardPart (unitDirection (Units.mk0 z hz)).val =
      standardPart (unitDirection
        (Units.mk0 (z + h) (add_ne_zero_of_relative_infinitesimal z h hz hi))).val := by
  apply unitDirection_standardPart_eq_of_relative
  simpa only [relative_add_units_sub_one] using hi

/-- The phase of the direction change is the actual relative unit direction. -/
theorem finitePhase_directionChange (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) :
    finitePhase (infinitesimalFiniteAngle (directionChange z h hz hi)) =
      (unitDirection (Units.mk0 (z + h)
        (add_ne_zero_of_relative_infinitesimal z h hz hi))).val /
      (unitDirection (Units.mk0 z hz)).val := by
  have he := finitePhase_localAngle _ _ (direction_standardPart_eq z h hz hi)
  simpa only [directionChange, Submonoid.coe_mul, Unitary.coe_inv, div_eq_mul_inv,
    mul_comm] using he

/-- The geometric direction change is the imaginary part of `Logm(1 + h/z)`. -/
theorem directionChange_eq_infLog_im (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) :
    (directionChange z h hz hi).val = (infLog (h / z) hi).im := by
  have hir : IsInfinitesimal
      (((Units.mk0 (z + h) (add_ne_zero_of_relative_infinitesimal z h hz hi) /
        Units.mk0 z hz : Surcomplex.{u}ˣ) : Surcomplex.{u}) - 1) := by
    simpa only [relative_add_units_sub_one] using hi
  have he := localAngle_unitDirection_eq_infLog_im _ _ hir
  simpa only [directionChange, relative_add_units_sub_one] using he

/-- The direction change has a quadratic expansion with an exact finite cubic remainder. -/
theorem directionChange_expansion (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = 1 / 3 ∧
      (directionChange z h hz hi).val =
        (h / z).im - ((h / z) ^ 2).im / 2 + ((h / z) ^ 3 * R).im ∧
      |((h / z) ^ 3 * R).im| ≤ modulus (h / z) ^ 3 * modulus R := by
  rw [directionChange_eq_infLog_im]
  exact infLog_im_expansion (h / z) hi

/-- The angular error after the quadratic term is at most a finite factor times `|h/z|³`. -/
theorem directionChange_remainder_bound (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) :
    ∃ B : SignSequence.{u}, SignSequence.IsFinite B ∧ 0 ≤ B ∧
      |(directionChange z h hz hi).val - ((h / z).im - ((h / z) ^ 2).im / 2)| ≤
        modulus (h / z) ^ 3 * B := by
  rw [directionChange_eq_infLog_im]
  exact infLog_im_remainder_bound (h / z) hi

/-- A relative perturbation's direction change has no smaller valuation, including at zero. -/
theorem valuation_directionChange_ge (z h : Surcomplex.{u}) (hz : z ≠ 0)
    (hi : IsInfinitesimal (h / z)) :
    valuation (h / z) ≤ SignSequence.valuation (directionChange z h hz hi).val := by
  rw [directionChange_eq_infLog_im]
  exact valuation_im_infLog_ge (h / z) hi

/-- A nonreal leading coefficient makes the direction change retain the perturbation's valuation. -/
theorem valuation_directionChange_eq_of_leadingCoeff_im_ne_zero (z h : Surcomplex.{u})
    (hz : z ≠ 0) (hi : IsInfinitesimal (h / z)) (him : (leadingCoeff (h / z)).im ≠ 0) :
    SignSequence.valuation (directionChange z h hz hi).val = valuation (h / z) := by
  rw [directionChange_eq_infLog_im]
  exact valuation_im_infLog_eq_of_leadingCoeff_im_ne_zero (h / z) hi him

end
end Surreal.Surcomplex
