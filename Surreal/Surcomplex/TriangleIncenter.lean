import Surreal.Algebra.LineDistance
import Surreal.Surcomplex.TriangleHeron

/-!
# The actual incircle and its three interior contact points

The positive side-weighted barycenter in `trigonometry:eq:incenter` has
perpendicular distance `area / semiperimeter` from all three side lines.
Each perpendicular foot lies in its open side segment, and each line
meets the circle at exactly that foot. This supplies the geometric
incircle clauses of `trigonometry:thm:heron` at arbitrary surreal scales.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- Positive barycentric coordinates define the strict interior of a noncollinear triangle. -/
def IsInteriorPoint (T : Triangle.{u}) (P : Surcomplex.{u}) : Prop :=
  ∃ a b c : SignSequence.{u}, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧
    P = a • T.A + b • T.B + c • T.C

/-- The side-weighted barycenter, with denominator twice the semiperimeter. -/
def incenter (T : Triangle.{u}) : Surcomplex.{u} :=
  (2 * T.semiperimeter)⁻¹ • (T.sideA • T.A + T.sideB • T.B + T.sideC • T.C)

@[simp] theorem incenter_rotate (T : Triangle.{u}) : T.rotate.incenter = T.incenter := by
  simp only [incenter, semiperimeter_rotate, sideA_rotate, sideB_rotate, sideC_rotate]
  change (2 * T.semiperimeter)⁻¹ • (T.sideB • T.B + T.sideC • T.C + T.sideA • T.A) = _
  congr 1
  abel

/-- The displayed barycenter has three strictly positive weights summing to one. -/
theorem incenter_isInteriorPoint (T : Triangle.{u}) : T.IsInteriorPoint T.incenter := by
  have hp : 0 < 2 * T.semiperimeter := mul_pos (by norm_num) T.semiperimeter_pos
  refine ⟨T.sideA / (2 * T.semiperimeter), T.sideB / (2 * T.semiperimeter),
    T.sideC / (2 * T.semiperimeter), div_pos T.sideA_pos hp, div_pos T.sideB_pos hp,
    div_pos T.sideC_pos hp, ?_, ?_⟩
  · rw [← add_div, ← add_div]
    have he : T.sideA + T.sideB + T.sideC = 2 * T.semiperimeter := by
      dsimp [semiperimeter]
      ring
    rw [he, div_self hp.ne']
  · simp only [incenter, smul_add, smul_smul, div_eq_mul_inv, mul_comm]

/-- Translate the barycenter to the first vertex. -/
theorem incenter_sub_A (T : Triangle.{u}) :
    T.incenter - T.A = (T.sideB / (2 * T.semiperimeter)) • (T.B - T.A) +
      (T.sideC / (2 * T.semiperimeter)) • (T.C - T.A) := by
  apply QuadraticAlgebra.ext <;>
    simp only [incenter, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
      QuadraticAlgebra.im_smul, smul_eq_mul] <;>
    field_simp [T.semiperimeter_pos.ne'] <;> dsimp [semiperimeter] <;> ring

/-- The squared side lengths give the adjacent-edge dot product. -/
theorem dot_adjacent_edges (T : Triangle.{u}) :
    Complexify.dot (T.B - T.A) (T.C - T.A) =
      (T.sideC ^ 2 + T.sideB ^ 2 - T.sideA ^ 2) / 2 := by
  have he := Complexify.normSq_sub (T.B - T.A) (T.C - T.A)
  have hd : (T.B - T.A) - (T.C - T.A) = T.B - T.C := by abel
  change normSq ((T.B - T.A) - (T.C - T.A)) =
    normSq (T.B - T.A) + normSq (T.C - T.A) -
      2 * Complexify.dot (T.B - T.A) (T.C - T.A) at he
  rw [hd, ← modulus_sq, ← modulus_sq, ← modulus_sq, modulus_sub_comm T.B T.A] at he
  change T.sideA ^ 2 = T.sideC ^ 2 + T.sideB ^ 2 -
    2 * Complexify.dot (T.B - T.A) (T.C - T.A) at he
  linarith only [he]

/-- The incenter's projection along the first side has the expected tangent length. -/
theorem dot_incenter_sub_A (T : Triangle.{u}) :
    Complexify.dot (T.B - T.A) (T.incenter - T.A) =
      T.sideC * (T.semiperimeter - T.sideA) := by
  rw [T.incenter_sub_A]
  have he : Complexify.dot (T.B - T.A)
      ((T.sideB / (2 * T.semiperimeter)) • (T.B - T.A) +
        (T.sideC / (2 * T.semiperimeter)) • (T.C - T.A)) =
      (T.sideB / (2 * T.semiperimeter)) * normSq (T.B - T.A) +
        (T.sideC / (2 * T.semiperimeter)) *
          Complexify.dot (T.B - T.A) (T.C - T.A) := by
    simp only [Complexify.dot_def, normSq_eq, QuadraticAlgebra.re_add,
      QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul,
      smul_eq_mul]
    ring
  rw [he, ← modulus_sq, modulus_sub_comm T.B T.A, T.dot_adjacent_edges]
  change T.sideB / (2 * T.semiperimeter) * T.sideC ^ 2 +
    T.sideC / (2 * T.semiperimeter) *
      ((T.sideC ^ 2 + T.sideB ^ 2 - T.sideA ^ 2) / 2) = _
  field_simp [T.semiperimeter_pos.ne']
  dsimp [semiperimeter]
  ring

/-- The incenter divides the signed altitude in its positive opposite barycentric weight. -/
theorem cross_incenter_sub_A (T : Triangle.{u}) :
    Complexify.cross (T.B - T.A) (T.incenter - T.A) =
      (T.sideC / (2 * T.semiperimeter)) * Complexify.cross (T.B - T.A) (T.C - T.A) := by
  rw [T.incenter_sub_A]
  simp only [Complexify.cross_def, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- The perpendicular contact parameter on AB is `(s-a)/c`. -/
theorem incenter_projection_parameter (T : Triangle.{u}) :
    Complexify.lineProjectionParameter T.A (T.B - T.A) T.incenter =
      (T.semiperimeter - T.sideA) / T.sideC := by
  rw [Complexify.lineProjectionParameter, T.dot_incenter_sub_A]
  change _ / normSq (T.B - T.A) = _
  rw [← modulus_sq, modulus_sub_comm T.B T.A]
  change _ / T.sideC ^ 2 = _
  field_simp [T.sideC_pos.ne']

/-- Both endpoint distances of each incircle contact are strictly positive. -/
theorem incenter_projection_parameter_mem (T : Triangle.{u}) :
    Complexify.lineProjectionParameter T.A (T.B - T.A) T.incenter ∈
      Set.Ioo (0 : SignSequence.{u}) 1 := by
  rw [T.incenter_projection_parameter]
  refine ⟨div_pos T.semiperimeter_sub_sideA_pos T.sideC_pos,
    (div_lt_one T.sideC_pos).mpr ?_⟩
  dsimp [semiperimeter]
  linarith [T.strict_side_inequalities.2.1]

/-- The perpendicular foot is strictly inside the actual side segment. -/
theorem incenter_contact_mem_openSegment (T : Triangle.{u}) :
    Complexify.lineProjection T.A (T.B - T.A) T.incenter ∈
      openSegment SignSequence.{u} T.A T.B :=
  Complexify.lineProjection_mem_openSegment T.A T.B T.incenter
    T.incenter_projection_parameter_mem

/-- The actual perpendicular distance to a side is the positive area-to-semiperimeter ratio. -/
theorem lineDistance_incenter (T : Triangle.{u}) :
    Complexify.lineDistance T.A (T.B - T.A) T.incenter = T.inradius := by
  rw [Complexify.lineDistance_eq_cross_div _ _ _
    (left_ne_zero_of_cross_ne_zero T.noncollinear), T.cross_incenter_sub_A,
    abs_mul, abs_of_pos (div_pos T.sideC_pos (mul_pos (by norm_num) T.semiperimeter_pos))]
  change _ / modulus (T.B - T.A) = _
  rw [modulus_sub_comm T.B T.A]
  change (T.sideC / (2 * T.semiperimeter)) *
    |Complexify.cross (T.B - T.A) (T.C - T.A)| / T.sideC =
      (|Complexify.cross (T.B - T.A) (T.C - T.A)| / 2) / T.semiperimeter
  field_simp [T.sideC_pos.ne', T.semiperimeter_pos.ne']

/-- All three side lines have the same positive distance from the displayed center. -/
theorem lineDistance_incenter_cyclic (T : Triangle.{u}) :
    Complexify.lineDistance T.A (T.B - T.A) T.incenter = T.inradius ∧
    Complexify.lineDistance T.B (T.C - T.B) T.incenter = T.inradius ∧
    Complexify.lineDistance T.C (T.A - T.C) T.incenter = T.inradius := by
  refine ⟨T.lineDistance_incenter, ?_, ?_⟩
  · have he := T.rotate.lineDistance_incenter
    rw [incenter_rotate, inradius_rotate] at he
    exact he
  · have he := T.rotate.rotate.lineDistance_incenter
    rw [incenter_rotate, incenter_rotate, inradius_rotate, inradius_rotate] at he
    exact he

/-- The circle meets the entire supporting line only at its interior perpendicular foot. -/
theorem incircle_contact (T : Triangle.{u}) :
    ∃! P : Surcomplex.{u}, (∃ t : SignSequence.{u}, P = T.A + t • (T.B - T.A)) ∧
      modulus (T.incenter - P) = T.inradius := by
  have he := Complexify.existsUnique_line_contact T.A (T.B - T.A) T.incenter
    (left_ne_zero_of_cross_ne_zero T.noncollinear)
  change (∃! P : Surcomplex.{u}, (∃ t : SignSequence.{u}, P = T.A + t • (T.B - T.A)) ∧
    modulus (T.incenter - P) = Complexify.lineDistance T.A (T.B - T.A) T.incenter) at he
  rwa [T.lineDistance_incenter] at he

end
end Surreal.Surcomplex.Triangle
