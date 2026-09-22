import Surreal.Algebra.Complexify
import Mathlib.Tactic.FieldSimp

/-!
# Rational coordinates on the unit circle

This file proves `found:eq:rationalcircle` and the affine parametrization and
inverse-chart clauses of `trigonometry:thm:cayley`. Everything is algebraic
over an arbitrary ordered field. No square roots or trigonometric functions
are needed.

The projective point, multiplication law, and relation to half angles in
`trigonometry:thm:cayley` are not covered by this file.
-/

namespace Surreal.Complexify

variable {F : Type*} [Field F]

/-- The rational circle parametrization `found:eq:rationalcircle`. -/
def circleParam (t : F) : Complexify F :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

@[simp] theorem circleParam_re (t : F) :
    (circleParam t).re = (1 - t ^ 2) / (1 + t ^ 2) := rfl

@[simp] theorem circleParam_im (t : F) :
    (circleParam t).im = 2 * t / (1 + t ^ 2) := rfl

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem circleParam_den_pos (t : F) : 0 < 1 + t ^ 2 := by positivity

/-- The rational parametrization takes values on the unit circle. -/
@[simp] theorem normSq_circleParam (t : F) : normSq (circleParam t) = 1 := by
  simp only [normSq, circleParam_re, circleParam_im]
  field_simp [ne_of_gt (circleParam_den_pos t)]
  ring

/-- The elementary identity proving the chart omits the point `-1`. -/
theorem one_add_circleParam_re (t : F) :
    1 + (circleParam t).re = 2 / (1 + t ^ 2) := by
  simp only [circleParam_re]
  field_simp [ne_of_gt (circleParam_den_pos t)]
  ring

theorem circleParam_ne_neg_one (t : F) : circleParam t ≠ -1 := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  have hpos : 0 < 1 + (circleParam t).re := by
    rw [one_add_circleParam_re]
    exact div_pos (by norm_num) (circleParam_den_pos t)
  simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] at hre
  rw [hre] at hpos
  simp at hpos

/-- The inverse affine coordinate in `trigonometry:thm:cayley`. -/
def circleCoord (z : Complexify F) : F := z.im / (1 + z.re)

@[simp] theorem circleCoord_circleParam (t : F) : circleCoord (circleParam t) = t := by
  simp only [circleCoord, circleParam_im, one_add_circleParam_re]
  field_simp [ne_of_gt (circleParam_den_pos t)]

/-- The inverse coordinate's denominator is nonzero on the punctured circle. -/
theorem circleCoord_den_ne_zero {z : Complexify F} (hz : normSq z = 1)
    (hne : z ≠ -1) : 1 + z.re ≠ 0 := by
  intro hden
  have hre : z.re = -1 := by linarith
  have him : z.im = 0 := by
    apply sq_eq_zero_iff.mp
    dsimp [normSq] at hz
    nlinarith [hz]
  apply hne
  ext
  · simpa only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] using hre
  · simpa only [QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero] using him

/-- Substituting the inverse coordinate recovers each unit-circle point
other than `-1`, the affine inverse clause of `trigonometry:thm:cayley`. -/
theorem circleParam_circleCoord {z : Complexify F} (hz : normSq z = 1)
    (hne : z ≠ -1) : circleParam (circleCoord z) = z := by
  have hden := circleCoord_den_ne_zero hz hne
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := hz
  have h : 1 + (z.im / (1 + z.re)) ^ 2 = 2 / (1 + z.re) := by
    field_simp [hden]
    nlinarith [hnorm]
  ext
  · simp only [circleParam_re, circleCoord, h]
    field_simp [hden]
    nlinarith [hnorm]
  · simp only [circleParam_im, circleCoord, h]
    field_simp [hden]

theorem circleParam_injective : Function.Injective (circleParam : F → Complexify F) :=
  Function.LeftInverse.injective circleCoord_circleParam

/-- The affine bijection in `trigonometry:thm:cayley`. This does not include
the projective or trigonometric clauses of that theorem. -/
def circleEquiv : F ≃ {z : Complexify F // normSq z = 1 ∧ z ≠ -1} where
  toFun t := ⟨circleParam t, normSq_circleParam t, circleParam_ne_neg_one t⟩
  invFun z := circleCoord z.val
  left_inv := circleCoord_circleParam
  right_inv z := Subtype.ext (circleParam_circleCoord z.property.1 z.property.2)

end Surreal.Complexify
