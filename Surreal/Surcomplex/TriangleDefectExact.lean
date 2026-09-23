import Surreal.Surcomplex.AngularDistance
import Surreal.Surcomplex.TriangleAngleSum

/-!
# The exact triangle-inequality defect at arbitrary surreal scales

An unoriented angle in `[0,pi]` is defined for every pair of nonzero
actual vectors, including collinear pairs. Its cosine is the normalized
dot product. Factoring the difference of the two squared lengths proves
`trigonometry:eq:defectexact`, the exact clause of
`trigonometry:thm:defect`, without requiring infinitesimal angles or
comparable vector lengths.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The unoriented actual angle between any two nonzero vectors, including collinear vectors. -/
def vectorAngle (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    SignSequence.FiniteElement.{u} :=
  unitCircleAngle (unitDirection (Units.mk0 w hw / Units.mk0 z hz))

/-- The unoriented vector angle takes its actual value in the full closed interval `[0,pi]`. -/
theorem vectorAngle_mem (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    (vectorAngle z w hz hw).val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) :=
  unitCircleAngle_mem _

/-- The cosine of the unoriented vector angle is the normalized actual dot product. -/
theorem finiteCos_vectorAngle (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    finiteCos (vectorAngle z w hz hw) = Complexify.dot z w / (modulus z * modulus w) := by
  rw [vectorAngle, finiteCos_unitCircleAngle, unitDirection_div_eq]
  change (conj z * w / ofReal (modulus z * modulus w)).re = _
  have hi : (ofReal (modulus z * modulus w))⁻¹ =
      ofReal ((modulus z * modulus w)⁻¹) := (map_inv₀ ofReal _).symm
  simp only [div_eq_mul_inv, hi, mul_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero, conj_re, conj_im, Complexify.dot_def]
  ring

/-- The general unoriented angle agrees with the existing interior angle when it is noncollinear. -/
theorem vectorAngle_eq_interiorAngle (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0)
    (h : Complexify.cross z w ≠ 0) : vectorAngle z w hz hw = interiorAngle z w h := by
  have hi := interiorAngle_mem z w h
  apply finiteCos_strictAntiOn.injOn (vectorAngle_mem z w hz hw) ⟨hi.1.le, hi.2.le⟩
  rw [finiteCos_vectorAngle, finiteCos_interiorAngle]

/-- Interchanging the two vectors preserves their unoriented actual angle. -/
theorem vectorAngle_comm (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    vectorAngle z w hz hw = vectorAngle w z hw hz := by
  apply finiteCos_strictAntiOn.injOn (vectorAngle_mem z w hz hw) (vectorAngle_mem w z hw hz)
  rw [finiteCos_vectorAngle, finiteCos_vectorAngle, Complexify.dot_comm z w, mul_comm]

/-- The squared length of a vector sum is given by its actual unoriented angle. -/
theorem modulus_add_sq_eq_vectorAngle (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    modulus (z + w) ^ 2 = modulus z ^ 2 + modulus w ^ 2 +
      2 * modulus z * modulus w * finiteCos (vectorAngle z w hz hw) := by
  rw [finiteCos_vectorAngle]
  have he : 2 * modulus z * modulus w *
      (Complexify.dot z w / (modulus z * modulus w)) = 2 * Complexify.dot z w := by
    field_simp [(modulus_pos hz).ne', (modulus_pos hw).ne']
  rw [he, modulus_sq, modulus_sq, modulus_sq]
  exact Complexify.normSq_add z w

/-- The nonnegative defect in the actual triangle inequality. -/
def triangleDefect (z w : Surcomplex.{u}) : SignSequence.{u} :=
  modulus z + modulus w - modulus (z + w)

theorem triangleDefect_nonneg (z w : Surcomplex.{u}) : 0 ≤ triangleDefect z w :=
  sub_nonneg.mpr (modulus_add_le z w)

/-- The defect never exceeds the sum of the two vector lengths. -/
theorem triangleDefect_le_sum (z w : Surcomplex.{u}) :
    triangleDefect z w ≤ modulus z + modulus w :=
  sub_le_self _ (modulus_nonneg _)

/-- The rationalized defect denominator is positive for any pair of nonzero actual vectors. -/
theorem triangleDefect_denominator_pos (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    0 < modulus z + modulus w + modulus (z + w) :=
  add_pos_of_pos_of_nonneg (add_pos (modulus_pos hz) (modulus_pos hw)) (modulus_nonneg _)

/-- The denominator is bounded by twice the sum of the two lengths. -/
theorem triangleDefect_denominator_le (z w : Surcomplex.{u}) :
    modulus z + modulus w + modulus (z + w) ≤ 2 * (modulus z + modulus w) := by
  linarith only [modulus_add_le z w]

/-- The polynomial defect identity before dividing by the positive rationalizing denominator. -/
theorem triangleDefect_mul_denominator (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    triangleDefect z w * (modulus z + modulus w + modulus (z + w)) =
      4 * modulus z * modulus w * finiteSin (finiteHalf (vectorAngle z w hz hw)) ^ 2 := by
  have hn := modulus_add_sq_eq_vectorAngle z w hz hw
  have hs := finiteSin_finiteHalf_sq (vectorAngle z w hz hw)
  dsimp only [triangleDefect]
  linear_combination -hn - 4 * modulus z * modulus w * hs

/-- The exact defect formula, valid for every unoriented angle and all actual surreal lengths. -/
theorem triangleDefect_exact (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    triangleDefect z w =
      4 * modulus z * modulus w * finiteSin (finiteHalf (vectorAngle z w hz hw)) ^ 2 /
        (modulus z + modulus w + modulus (z + w)) := by
  apply (eq_div_iff (triangleDefect_denominator_pos z w hz hw).ne').mpr
  exact triangleDefect_mul_denominator z w hz hw

/-- The cosine form of the same exact defect identity. -/
theorem triangleDefect_cosine (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    triangleDefect z w =
      2 * modulus z * modulus w * (1 - finiteCos (vectorAngle z w hz hw)) /
        (modulus z + modulus w + modulus (z + w)) := by
  rw [triangleDefect_exact z w hz hw, finiteSin_finiteHalf_sq]
  ring

/-- A nonzero unoriented angle has positive half-angle sine, including the antiparallel case. -/
theorem sin_half_vectorAngle_pos (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0)
    (hangle : (vectorAngle z w hz hw).val ≠ 0) :
    0 < finiteSin (finiteHalf (vectorAngle z w hz hw)) := by
  have hi := vectorAngle_mem z w hz hw
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hpos : 0 < (vectorAngle z w hz hw).val := lt_of_le_of_ne hi.1 hangle.symm
  apply finiteSin_pos_of_mem_Ioo
  rw [val_finiteHalf]
  constructor <;> linarith only [hpos, hi.2, hp]

/-- The triangle inequality is strict whenever the unoriented angle is nonzero. -/
theorem triangleDefect_pos_of_vectorAngle_ne_zero (z w : Surcomplex.{u})
    (hz : z ≠ 0) (hw : w ≠ 0) (hangle : (vectorAngle z w hz hw).val ≠ 0) :
    0 < triangleDefect z w := by
  rw [triangleDefect_exact z w hz hw]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (modulus_pos hz)) (modulus_pos hw))
    (sq_pos_of_pos (sin_half_vectorAngle_pos z w hz hw hangle)))
    (triangleDefect_denominator_pos z w hz hw)

end
end Surreal.Surcomplex
