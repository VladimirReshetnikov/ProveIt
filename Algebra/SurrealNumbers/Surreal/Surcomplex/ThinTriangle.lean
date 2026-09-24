import Surreal.Surcomplex.TriangleCoordinates
import Surreal.Surcomplex.ArcsinSeries
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Thin triangles with arbitrary horizontal scales

The general family in `trigonometry:ex:hierarchies` has an altitude
infinitesimal relative to each adjacent horizontal displacement. Its exact
coordinate geometry and radius equivalents retain the actual side scales;
no horizontal length is assumed finite or appreciable.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- The literal minimum-scale thinness condition is exactly the pair of small-slope conditions. -/
theorem infinitesimal_height_div_min_iff (L x h : SignSequence.{u})
    (hx : 0 < x) (hxL : x < L) (hh : 0 < h) :
    SignSequence.IsInfinitesimal (h / min x (L - x)) ↔
      SignSequence.IsInfinitesimal (h / x) ∧ SignSequence.IsInfinitesimal (h / (L - x)) := by
  have hc := sub_pos.mpr hxL
  have hm := lt_min hx hc
  constructor
  · intro hi
    constructor
    · apply SignSequence.infinitesimal_of_abs_le (y := h / min x (L - x)) _ hi
      rw [abs_of_pos (div_pos hh hx), abs_of_pos (div_pos hh hm)]
      exact div_le_div_of_nonneg_left hh.le hm (min_le_left _ _)
    · apply SignSequence.infinitesimal_of_abs_le (y := h / min x (L - x)) _ hi
      rw [abs_of_pos (div_pos hh hc), abs_of_pos (div_pos hh hm)]
      exact div_le_div_of_nonneg_left hh.le hm (min_le_right _ _)
  · intro hi
    rcases le_total x (L - x) with he | he
    · simpa only [min_eq_left he] using hi.1
    · simpa only [min_eq_right he] using hi.2

/-- A triangle whose positive altitude is infinitesimal relative to both horizontal displacements. -/
structure ThinTriangle where
  L : SignSequence.{u}
  x : SignSequence.{u}
  h : SignSequence.{u}
  x_pos : 0 < x
  x_lt_base : x < L
  height_pos : 0 < h
  slope_left_infinitesimal : SignSequence.IsInfinitesimal (h / x)
  slope_right_infinitesimal : SignSequence.IsInfinitesimal (h / (L - x))

namespace ThinTriangle

noncomputable section

variable (D : ThinTriangle.{u})

theorem base_pos : 0 < D.L := D.x_pos.trans D.x_lt_base

theorem complement_pos : 0 < D.L - D.x := sub_pos.mpr D.x_lt_base

/-- The altitude is infinitesimal relative to the smaller horizontal displacement. -/
theorem height_div_min_infinitesimal :
    SignSequence.IsInfinitesimal (D.h / min D.x (D.L - D.x)) :=
  (infinitesimal_height_div_min_iff D.L D.x D.h D.x_pos D.x_lt_base D.height_pos).mpr
    ⟨D.slope_left_infinitesimal, D.slope_right_infinitesimal⟩

/-- The actual noncollinear triangle with vertices zero, the base length, and x+i*h. -/
def triangle : Triangle.{u} :=
  Triangle.fromCoordinates D.L D.x D.h D.x_pos D.x_lt_base D.height_pos

@[simp] theorem vertexA : D.triangle.A = 0 := rfl
@[simp] theorem vertexB : D.triangle.B = ofReal D.L := rfl
@[simp] theorem vertexC : D.triangle.C = ⟨D.x, D.h⟩ := rfl

@[simp] theorem sideA : D.triangle.sideA = SignSequence.sqrt ((D.L - D.x) ^ 2 + D.h ^ 2) :=
  Triangle.sideA_fromCoordinates _ _ _ _ _ _

@[simp] theorem sideB : D.triangle.sideB = SignSequence.sqrt (D.x ^ 2 + D.h ^ 2) :=
  Triangle.sideB_fromCoordinates _ _ _ _ _ _

@[simp] theorem sideC : D.triangle.sideC = D.L := Triangle.sideC_fromCoordinates _ _ _ _ _ _

/-- The first actual base angle is inverse tangent of the left slope. -/
theorem angleA : D.triangle.angleA = arctan (D.h / D.x) :=
  Triangle.angleA_fromCoordinates _ _ _ _ _ _

/-- The second actual base angle is inverse tangent of the right slope. -/
theorem angleB : D.triangle.angleB = arctan (D.h / (D.L - D.x)) :=
  Triangle.angleB_fromCoordinates _ _ _ _ _ _

/-- The upper angle is the supplement of the two inverse-tangent base angles. -/
theorem angleC : D.triangle.angleC = SignSequence.finiteOfReal Real.pi -
    arctan (D.h / D.x) - arctan (D.h / (D.L - D.x)) :=
  Triangle.angleC_fromCoordinates _ _ _ _ _ _

/-- The actual area retains the product of base and height even when their scales differ. -/
@[simp] theorem area : D.triangle.area = D.L * D.h / 2 :=
  Triangle.area_fromCoordinates _ _ _ _ _ _

/-- The circumradius is the product of the two sloping sides divided by twice the altitude. -/
theorem circumradius_eq_side_product : D.triangle.circumradius =
    D.triangle.sideA * D.triangle.sideB / (2 * D.h) :=
  Triangle.circumradius_fromCoordinates _ _ _ _ _ _

/-- The exact coordinate formula for the actual circumradius. -/
theorem circumradius_eq : D.triangle.circumradius =
    SignSequence.sqrt (D.x ^ 2 + D.h ^ 2) *
      SignSequence.sqrt ((D.L - D.x) ^ 2 + D.h ^ 2) / (2 * D.h) := by
  rw [D.circumradius_eq_side_product, D.sideA, D.sideB]
  ring

/-- The actual inradius is base times height divided by perimeter. -/
theorem inradius_eq : D.triangle.inradius =
    D.L * D.h / (D.triangle.sideA + D.triangle.sideB + D.L) :=
  Triangle.inradius_fromCoordinates _ _ _ _ _ _

private theorem hypotenuse_asymptotic {p h : SignSequence.{u}} (hp : 0 < p)
    (hi : SignSequence.IsInfinitesimal (h / p)) :
    SignSequence.IsInfinitesimal (SignSequence.sqrt (p ^ 2 + h ^ 2) / p - 1) := by
  apply SignSequence.infinitesimal_sub_one_of_sq_sub_one
    (div_nonneg (SignSequence.sqrt_nonneg _) hp.le)
  have he : (SignSequence.sqrt (p ^ 2 + h ^ 2) / p) ^ 2 - 1 = (h / p) ^ 2 := by
    rw [div_pow, SignSequence.sqrt_sq (add_nonneg (sq_nonneg _) (sq_nonneg _)), div_pow]
    field_simp [hp.ne']
    ring
  rw [he]
  exact (SignSequence.infinitesimal_sq_iff _).mpr hi

/-- The right side is relatively equivalent to its horizontal displacement. -/
theorem sideA_div_complement_sub_one :
    SignSequence.IsInfinitesimal (D.triangle.sideA / (D.L - D.x) - 1) := by
  rw [D.sideA]
  exact hypotenuse_asymptotic D.complement_pos D.slope_right_infinitesimal

/-- The left side is relatively equivalent to its horizontal displacement. -/
theorem sideB_div_x_sub_one :
    SignSequence.IsInfinitesimal (D.triangle.sideB / D.x - 1) := by
  rw [D.sideB]
  exact hypotenuse_asymptotic D.x_pos D.slope_left_infinitesimal

/-- The circumradius detects both horizontal scales and the reciprocal altitude. -/
theorem circumradius_asymptotic : SignSequence.IsInfinitesimal
    (D.triangle.circumradius / (D.x * (D.L - D.x) / (2 * D.h)) - 1) := by
  have he : D.triangle.circumradius / (D.x * (D.L - D.x) / (2 * D.h)) =
      (D.triangle.sideA / (D.L - D.x)) * (D.triangle.sideB / D.x) := by
    rw [D.circumradius_eq_side_product]
    field_simp [D.x_pos.ne', D.complement_pos.ne', D.height_pos.ne']
  rw [he]
  exact SignSequence.infinitesimal_mul_sub_one D.sideA_div_complement_sub_one D.sideB_div_x_sub_one

private theorem finite_weight {p L : SignSequence.{u}} (hp : 0 ≤ p) (hL : 0 < L)
    (hpL : p ≤ L) : SignSequence.IsFinite (p / L) := by
  apply (SignSequence.isFinite_iff_exists_nat_abs_le _).mpr
  refine ⟨1, ?_⟩
  rw [Nat.cast_one, abs_of_nonneg (div_nonneg hp hL.le)]
  exact (div_le_one hL).mpr hpL

/-- Bounded horizontal weights allow adding side equivalents without comparable side scales. -/
theorem sideSum_div_base_sub_one :
    SignSequence.IsInfinitesimal ((D.triangle.sideA + D.triangle.sideB) / D.L - 1) := by
  have hleft := SignSequence.finite_mul_infinitesimal
    (finite_weight D.complement_pos.le D.base_pos (by linarith only [D.x_pos]))
    D.sideA_div_complement_sub_one
  have hright := SignSequence.finite_mul_infinitesimal
    (finite_weight D.x_pos.le D.base_pos D.x_lt_base.le) D.sideB_div_x_sub_one
  have he : (D.triangle.sideA + D.triangle.sideB) / D.L - 1 =
      (D.L - D.x) / D.L * (D.triangle.sideA / (D.L - D.x) - 1) +
        D.x / D.L * (D.triangle.sideB / D.x - 1) := by
    field_simp [D.x_pos.ne', D.complement_pos.ne', D.base_pos.ne']
    ring
  rw [he]
  exact SignSequence.infinitesimal_add hleft hright

/-- The perimeter is relatively equivalent to twice the horizontal base. -/
theorem perimeter_div_two_base_sub_one : SignSequence.IsInfinitesimal
    ((D.triangle.sideA + D.triangle.sideB + D.L) / (2 * D.L) - 1) := by
  have hf : SignSequence.IsFinite ((1 : SignSequence.{u}) / 2) := by
    simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)
  have he : (D.triangle.sideA + D.triangle.sideB + D.L) / (2 * D.L) - 1 =
      ((D.triangle.sideA + D.triangle.sideB) / D.L - 1) * (1 / 2) := by
    field_simp [D.base_pos.ne']
    ring
  rw [he]
  exact SignSequence.infinitesimal_mul_finite D.sideSum_div_base_sub_one hf

/-- The actual inradius is relatively equivalent to half the height, at arbitrary horizontal scales. -/
theorem inradius_asymptotic :
    SignSequence.IsInfinitesimal (D.triangle.inradius / (D.h / 2) - 1) := by
  have he : D.triangle.inradius / (D.h / 2) =
      ((D.triangle.sideA + D.triangle.sideB + D.L) / (2 * D.L))⁻¹ := by
    rw [D.inradius_eq]
    field_simp [D.height_pos.ne', D.base_pos.ne',
      (add_pos (add_pos D.triangle.sideA_pos D.triangle.sideB_pos) D.base_pos).ne']
  rw [he]
  exact SignSequence.infinitesimal_inv_sub_one D.perimeter_div_two_base_sub_one

/-- The left base angle is infinitesimal. -/
theorem angleA_infinitesimal : SignSequence.IsInfinitesimal D.triangle.angleA.val := by
  rw [D.angleA]
  exact infinitesimal_arctanFunction _ D.slope_left_infinitesimal

/-- The right base angle is infinitesimal. -/
theorem angleB_infinitesimal : SignSequence.IsInfinitesimal D.triangle.angleB.val := by
  rw [D.angleB]
  exact infinitesimal_arctanFunction _ D.slope_right_infinitesimal

/-- The first actual base angle is relatively equivalent to its positive infinitesimal slope. -/
theorem angleA_asymptotic :
    SignSequence.IsInfinitesimal (D.triangle.angleA.val / (D.h / D.x) - 1) := by
  rw [D.angleA]
  exact infinitesimal_arctanFunction_div_sub_one _ D.slope_left_infinitesimal
    (div_pos D.height_pos D.x_pos).ne'

/-- The second actual base angle is relatively equivalent to its positive infinitesimal slope. -/
theorem angleB_asymptotic :
    SignSequence.IsInfinitesimal (D.triangle.angleB.val / (D.h / (D.L - D.x)) - 1) := by
  rw [D.angleB]
  exact infinitesimal_arctanFunction_div_sub_one _ D.slope_right_infinitesimal
    (div_pos D.height_pos D.complement_pos).ne'

end
end ThinTriangle
end Surreal.Surcomplex
