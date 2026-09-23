import Surreal.Surcomplex.TriangleCoordinates
import Surreal.Surcomplex.TriangleFlatGap
import Surreal.Surcomplex.AcosEndpoint
import Surreal.Algebra.LineDistance

/-!
# The actual symmetric triangle with infinitesimal side gap

Construct the triangle of `trigonometry:ex:flatgap` above its horizontal
base of length `2 - τ`. The upper vertex is named `A`, so the opposite
side is the source's longest side `a`, and both other sides have length
one. Its altitude is an actual distance to the base line. All angle and
radius identities are exact; strong expansions are supplied separately.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- The source parameter is an arbitrary positive infinitesimal actual surreal. -/
structure SymmetricGapTriangle where
  τ : SignSequence.{u}
  τ_pos : 0 < τ
  τ_infinitesimal : SignSequence.IsInfinitesimal τ

namespace SymmetricGapTriangle

noncomputable section

variable (D : SymmetricGapTriangle.{u})

theorem gap_lt_one : D.τ < 1 := by
  have h := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt D.τ).mp
    D.τ_infinitesimal 1 (by norm_num)
  simpa only [map_one, abs_of_pos D.τ_pos] using h

theorem base_pos : 0 < 2 - D.τ := by linarith [D.gap_lt_one]

theorem half_base_pos : 0 < 1 - D.τ / 2 := by linarith [D.gap_lt_one]

theorem half_base_lt_base : 1 - D.τ / 2 < 2 - D.τ := by linarith [D.gap_lt_one]

theorem height_sq_pos : 0 < D.τ - D.τ ^ 2 / 4 := by
  have h := mul_pos D.τ_pos (show 0 < 1 - D.τ / 4 by linarith [D.gap_lt_one])
  nlinarith only [h]

/-- The exact altitude parameter in the symmetric-gap example. -/
def height : SignSequence.{u} := SignSequence.sqrt (D.τ - D.τ ^ 2 / 4)

theorem height_pos : 0 < D.height := SignSequence.sqrt_pos D.height_sq_pos

@[simp] theorem height_sq : D.height ^ 2 = D.τ - D.τ ^ 2 / 4 :=
  SignSequence.sqrt_sq D.height_sq_pos.le

private def coordinateTriangle : Triangle.{u} :=
  Triangle.fromCoordinates (2 - D.τ) (1 - D.τ / 2) D.height
    D.half_base_pos D.half_base_lt_base D.height_pos

/-- The actual triangle with `A` above the midpoint of the base `BC`. -/
def triangle : Triangle.{u} := D.coordinateTriangle.rotate.rotate

@[simp] theorem vertexA : D.triangle.A = ⟨1 - D.τ / 2, D.height⟩ := rfl

@[simp] theorem vertexB : D.triangle.B = 0 := rfl

@[simp] theorem vertexC : D.triangle.C = ofReal (2 - D.τ) := rfl

/-- The source's first side is the horizontal base. -/
@[simp] theorem sideA : D.triangle.sideA = 2 - D.τ := by
  change D.coordinateTriangle.sideC = _
  exact Triangle.sideC_fromCoordinates _ _ _ _ _ _

/-- The side from the upper vertex to the right endpoint is exactly one. -/
@[simp] theorem sideB : D.triangle.sideB = 1 := by
  change D.coordinateTriangle.sideA = _
  rw [coordinateTriangle, Triangle.sideA_fromCoordinates]
  apply SignSequence.sqrt_eq_of_nonneg_sq (by norm_num)
  rw [D.height_sq]
  ring

/-- The side from the upper vertex to the left endpoint is exactly one. -/
@[simp] theorem sideC : D.triangle.sideC = 1 := by
  change D.coordinateTriangle.sideB = _
  rw [coordinateTriangle, Triangle.sideB_fromCoordinates]
  apply SignSequence.sqrt_eq_of_nonneg_sq (by norm_num)
  rw [D.height_sq]
  ring

/-- The horizontal base is a largest side, as required by the relative-flatness theorem. -/
theorem sideA_largest : D.triangle.sideB ≤ D.triangle.sideA ∧
    D.triangle.sideC ≤ D.triangle.sideA := by
  rw [D.sideA, D.sideB, D.sideC]
  constructor <;> linarith [D.gap_lt_one]

/-- The side gap is the given actual infinitesimal parameter. -/
@[simp] theorem sideGap : D.triangle.sideGap = D.τ := by
  rw [Triangle.sideGap, D.sideA, D.sideB, D.sideC]
  ring

/-- The half-sine flatness parameter is the square of the geometric altitude. -/
theorem flatParameter : D.triangle.flatParameter = D.height ^ 2 := by
  rw [Triangle.flatParameter, D.sideGap, D.sideB, D.sideC, D.height_sq]
  ring

/-- The displayed altitude is the actual perpendicular distance from `A` to the line `BC`. -/
theorem height_eq_lineDistance :
    Complexify.lineDistance D.triangle.B (D.triangle.C - D.triangle.B) D.triangle.A =
      D.height := by
  have hv : D.triangle.C - D.triangle.B ≠ 0 :=
    left_ne_zero_of_cross_ne_zero D.triangle.rotate.noncollinear
  rw [Complexify.lineDistance_eq_cross_div D.triangle.B
    (D.triangle.C - D.triangle.B) D.triangle.A hv]
  rw [D.vertexA, D.vertexB, D.vertexC, sub_zero, sub_zero, Complexify.cross_def]
  change |(2 - D.τ) * D.height - 0 * (1 - D.τ / 2)| /
    modulus (ofReal (2 - D.τ)) = D.height
  rw [zero_mul, sub_zero, modulus_ofReal, abs_of_pos D.base_pos,
    abs_of_pos (mul_pos D.base_pos D.height_pos)]
  exact mul_div_cancel_left₀ D.height D.base_pos.ne'

/-- The actual area is the product of half the base and the altitude. -/
@[simp] theorem area : D.triangle.area = (1 - D.τ / 2) * D.height := by
  change D.coordinateTriangle.rotate.rotate.area = _
  rw [Triangle.area_rotate, Triangle.area_rotate, coordinateTriangle,
    Triangle.area_fromCoordinates]
  ring

/-- The actual circumradius is the reciprocal of twice the altitude. -/
theorem circumradius : D.triangle.circumradius = 1 / (2 * D.height) := by
  rw [Triangle.circumradius_eq_side_product, D.sideA, D.sideB, D.sideC, D.area]
  have hbase : 2 - D.τ = 2 * (1 - D.τ / 2) := by ring
  rw [hbase]
  field_simp [D.half_base_pos.ne', D.base_pos.ne', D.height_pos.ne']
  ring

/-- The cosine of the left base angle is one minus half the side gap. -/
theorem cos_angleB : finiteCos D.triangle.angleB = 1 - D.τ / 2 := by
  rw [Triangle.angleB, Triangle.cos_angleA_eq_side_quotient,
    Triangle.sideA_rotate, Triangle.sideB_rotate, Triangle.sideC_rotate,
    D.sideA, D.sideB, D.sideC]
  field_simp [D.base_pos.ne']
  ring

/-- The cosine of the right base angle has the same exact value. -/
theorem cos_angleC : finiteCos D.triangle.angleC = 1 - D.τ / 2 := by
  rw [Triangle.angleC, Triangle.cos_angleA_eq_side_quotient]
  simp only [Triangle.sideA_rotate, Triangle.sideB_rotate, Triangle.sideC_rotate,
    D.sideA, D.sideB, D.sideC]
  field_simp [D.base_pos.ne']
  ring

/-- The two actual base angles are equal, not merely equal in standard part. -/
theorem angleB_eq_angleC : D.triangle.angleB = D.triangle.angleC :=
  finiteCos_strictAntiOn.injOn
    ⟨D.triangle.rotate.angleA_mem.1.le, D.triangle.rotate.angleA_mem.2.le⟩
    ⟨D.triangle.rotate.rotate.angleA_mem.1.le, D.triangle.rotate.rotate.angleA_mem.2.le⟩
    (D.cos_angleB.trans D.cos_angleC.symm)

/-- The left base angle is half the actual supplement of the upper angle. -/
theorem angleB_eq_half_supplement :
    D.triangle.angleB = finiteHalf D.triangle.angleSupplement := by
  apply ArchimedeanClass.FiniteElement.ext
  rw [val_finiteHalf, Triangle.val_angleSupplement]
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) D.triangle.angle_sum
  change D.triangle.angleA.val + D.triangle.angleB.val + D.triangle.angleC.val =
    SignSequence.ofReal Real.pi at he
  rw [← D.angleB_eq_angleC] at he
  linarith only [he]

/-- The right base angle is also half the supplement of the upper angle. -/
theorem angleC_eq_half_supplement :
    D.triangle.angleC = finiteHalf D.triangle.angleSupplement :=
  D.angleB_eq_angleC.symm.trans D.angleB_eq_half_supplement

/-- The inverse cosine value is the actual left base angle. -/
theorem angleB_eq_arccos :
    D.triangle.angleB.val = arccosFunction (1 - D.τ / 2) := by
  have he := arccos_finiteCos D.triangle.angleB
    ⟨D.triangle.rotate.angleA_mem.1.le, D.triangle.rotate.angleA_mem.2.le⟩
  rw [← D.cos_angleB,
    arccosFunction_eq ⟨finiteCos D.triangle.angleB, finiteCos_mem_Icc _⟩]
  exact congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) he.symm

/-- The source supplement is exactly twice inverse cosine of one minus half the gap. -/
theorem angleSupplement_eq :
    D.triangle.angleSupplement.val = 2 * arccosFunction (1 - D.τ / 2) := by
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val)
    D.angleB_eq_half_supplement
  rw [val_finiteHalf, D.angleB_eq_arccos] at he
  linarith only [he]

end
end SymmetricGapTriangle
end Surreal.Surcomplex
