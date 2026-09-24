import Surreal.Surcomplex.TriangleCoordinates
import Surreal.Surcomplex.SmallSlopeExpansion
import Surreal.Foundations.SignSequenceHypotenuseExpansion

/-!
# Normalized triangles with infinitesimal height

The actual coordinates and hypotheses of `trigonometry:thm:flat` are
packaged without replacing the finite horizontal coordinate by its standard part.
All remainder assertions are exact equalities with finite coefficients.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- The normalized source data: a horizontal coordinate appreciably inside the unit interval,
and a positive infinitesimal height. -/
structure NormalizedFlatTriangle where
  x : SignSequence.{u}
  y : SignSequence.{u}
  x_finite : SignSequence.IsFinite x
  x_standardPart_mem : SignSequence.standardPart x ∈ Set.Ioo 0 1
  y_pos : 0 < y
  y_infinitesimal : SignSequence.IsInfinitesimal y

namespace NormalizedFlatTriangle

noncomputable section

variable (D : NormalizedFlatTriangle.{u})

theorem x_pos : 0 < D.x := by
  simpa only [map_zero] using
    ArchimedeanClass.lt_of_lt_stdPart SignSequence.ofReal D.x_finite D.x_standardPart_mem.1

theorem x_lt_one : D.x < 1 := by
  simpa only [map_one] using
    ArchimedeanClass.lt_of_stdPart_lt SignSequence.ofReal D.x_finite D.x_standardPart_mem.2

theorem complement_pos : 0 < 1 - D.x := sub_pos.mpr D.x_lt_one

theorem complement_finite : SignSequence.IsFinite (1 - D.x) :=
  SignSequence.finite_sub SignSequence.finite_one D.x_finite

theorem complement_standardPart : SignSequence.standardPart (1 - D.x) =
    1 - SignSequence.standardPart D.x := by
  rw [SignSequence.standardPart_sub SignSequence.finite_one D.x_finite,
    SignSequence.standardPart_one]

theorem complement_standardPart_pos : 0 < SignSequence.standardPart (1 - D.x) := by
  rw [D.complement_standardPart]
  exact sub_pos.mpr D.x_standardPart_mem.2

theorem inv_x_finite : SignSequence.IsFinite D.x⁻¹ :=
  SignSequence.finite_inv_of_standardPart_ne_zero D.x_finite D.x_standardPart_mem.1.ne'

theorem inv_complement_finite : SignSequence.IsFinite (1 - D.x)⁻¹ :=
  SignSequence.finite_inv_of_standardPart_ne_zero D.complement_finite
    D.complement_standardPart_pos.ne'

theorem y_finite : SignSequence.IsFinite D.y :=
  SignSequence.finite_of_infinitesimal D.y_infinitesimal

/-- The actual noncollinear triangle with vertices zero, one and x+iy. -/
def triangle : Triangle.{u} := Triangle.fromCoordinates 1 D.x D.y D.x_pos D.x_lt_one D.y_pos

@[simp] theorem sideA : D.triangle.sideA = SignSequence.sqrt ((1 - D.x) ^ 2 + D.y ^ 2) :=
  Triangle.sideA_fromCoordinates _ _ _ _ _ _

@[simp] theorem sideB : D.triangle.sideB = SignSequence.sqrt (D.x ^ 2 + D.y ^ 2) :=
  Triangle.sideB_fromCoordinates _ _ _ _ _ _

@[simp] theorem sideC : D.triangle.sideC = 1 :=
  Triangle.sideC_fromCoordinates _ _ _ _ _ _

@[simp] theorem area : D.triangle.area = D.y / 2 := by
  simpa only [triangle, one_mul] using
    Triangle.area_fromCoordinates 1 D.x D.y D.x_pos D.x_lt_one D.y_pos

/-- The first exact base angle in the normalized theorem. -/
theorem angleA : D.triangle.angleA = arctan (D.y / D.x) :=
  Triangle.angleA_fromCoordinates _ _ _ _ _ _

/-- The second exact base angle in the normalized theorem. -/
theorem angleB : D.triangle.angleB = arctan (D.y / (1 - D.x)) :=
  Triangle.angleB_fromCoordinates _ _ _ _ _ _

/-- The remaining angle is exactly the supplement of the two base angles. -/
theorem angleC : D.triangle.angleC =
    SignSequence.finiteOfReal Real.pi - arctan (D.y / D.x) - arctan (D.y / (1 - D.x)) :=
  Triangle.angleC_fromCoordinates _ _ _ _ _ _

/-- The first base angle's cubic expansion, with the literal fifth-order finite tail. -/
theorem angleA_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.angleA.val = D.y / D.x - D.y ^ 3 / (3 * D.x ^ 3) + D.y ^ 5 * E := by
  rw [D.angleA]
  exact arctanFunction_div_cubic_expansion _ _ D.x_finite D.x_standardPart_mem.1.ne'
    D.y_infinitesimal

/-- The second base angle's cubic expansion. -/
theorem angleB_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.angleB.val = D.y / (1 - D.x) - D.y ^ 3 / (3 * (1 - D.x) ^ 3) +
      D.y ^ 5 * E := by
  rw [D.angleB]
  exact arctanFunction_div_cubic_expansion _ _ D.complement_finite
    D.complement_standardPart_pos.ne' D.y_infinitesimal

/-- The base angles have positive finite leading factors, including their sum. -/
theorem base_angles_leading_factors : ∃ F G : SignSequence.{u},
    SignSequence.IsFinite F ∧ SignSequence.IsFinite G ∧
    SignSequence.standardPart F = (SignSequence.standardPart D.x)⁻¹ ∧
    SignSequence.standardPart G = (1 - SignSequence.standardPart D.x)⁻¹ ∧
    D.triangle.angleA.val = D.y * F ∧ D.triangle.angleB.val = D.y * G := by
  obtain ⟨F, hF, hFs, heF⟩ := arctanFunction_div_leading_factor _ _
    D.x_finite D.x_standardPart_mem.1.ne' D.y_infinitesimal
  obtain ⟨G, hG, hGs, heG⟩ := arctanFunction_div_leading_factor _ _
    D.complement_finite D.complement_standardPart_pos.ne' D.y_infinitesimal
  refine ⟨F, G, hF, hG, hFs, ?_, ?_, ?_⟩
  · simpa only [D.complement_standardPart] using hGs
  · rw [D.angleA]; exact heF
  · rw [D.angleB]; exact heG

/-- The exact normalized circumradius before expansion. -/
theorem circumradius_eq : D.triangle.circumradius =
    D.triangle.sideA * D.triangle.sideB / (2 * D.y) :=
  Triangle.circumradius_fromCoordinates _ _ _ _ _ _

/-- The exact normalized inradius before expansion. -/
theorem inradius_eq : D.triangle.inradius =
    D.y / (D.triangle.sideA + D.triangle.sideB + 1) := by
  simpa only [triangle, one_mul] using
    Triangle.inradius_fromCoordinates 1 D.x D.y D.x_pos D.x_lt_one D.y_pos

theorem sideA_finite : SignSequence.IsFinite D.triangle.sideA := by
  rw [D.sideA]
  exact SignSequence.finite_sqrt_sq_add_sq D.complement_pos D.complement_finite
    D.complement_standardPart_pos D.y_infinitesimal

theorem sideB_finite : SignSequence.IsFinite D.triangle.sideB := by
  rw [D.sideB]
  exact SignSequence.finite_sqrt_sq_add_sq D.x_pos D.x_finite
    D.x_standardPart_mem.1 D.y_infinitesimal

theorem standardPart_sideA : SignSequence.standardPart D.triangle.sideA =
    1 - SignSequence.standardPart D.x := by
  rw [D.sideA, SignSequence.standardPart_sqrt_sq_add_sq D.complement_pos
    D.complement_finite D.complement_standardPart_pos D.y_infinitesimal,
    D.complement_standardPart]

theorem standardPart_sideB : SignSequence.standardPart D.triangle.sideB =
    SignSequence.standardPart D.x := by
  rw [D.sideB]
  exact SignSequence.standardPart_sqrt_sq_add_sq D.x_pos D.x_finite
    D.x_standardPart_mem.1 D.y_infinitesimal

/-- The first side's quartic expansion with a finite sixth-order tail. -/
theorem sideA_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.sideA = (1 - D.x) + D.y ^ 2 / (2 * (1 - D.x)) -
      D.y ^ 4 / (8 * (1 - D.x) ^ 3) + D.y ^ 6 * E := by
  obtain ⟨E, hE, _, he⟩ := SignSequence.sqrt_sq_add_sq_expansion D.complement_pos
    D.complement_finite D.complement_standardPart_pos D.y_infinitesimal
  exact ⟨E, hE, D.sideA.trans he⟩

/-- The second side's quartic expansion with a finite sixth-order tail. -/
theorem sideB_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.sideB = D.x + D.y ^ 2 / (2 * D.x) -
      D.y ^ 4 / (8 * D.x ^ 3) + D.y ^ 6 * E := by
  obtain ⟨E, hE, _, he⟩ := SignSequence.sqrt_sq_add_sq_expansion D.x_pos
    D.x_finite D.x_standardPart_mem.1 D.y_infinitesimal
  exact ⟨E, hE, D.sideB.trans he⟩

/-- A shorter first-side expansion for multiplication of the radius factors. -/
theorem sideA_quadratic_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.sideA = (1 - D.x) + D.y ^ 2 / (2 * (1 - D.x)) + D.y ^ 4 * E := by
  obtain ⟨E, hE, _, he⟩ := SignSequence.sqrt_sq_add_sq_quadratic_expansion D.complement_pos
    D.complement_finite D.complement_standardPart_pos D.y_infinitesimal
  exact ⟨E, hE, D.sideA.trans he⟩

/-- A shorter second-side expansion for multiplication of the radius factors. -/
theorem sideB_quadratic_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.sideB = D.x + D.y ^ 2 / (2 * D.x) + D.y ^ 4 * E := by
  obtain ⟨E, hE, _, he⟩ := SignSequence.sqrt_sq_add_sq_quadratic_expansion D.x_pos
    D.x_finite D.x_standardPart_mem.1 D.y_infinitesimal
  exact ⟨E, hE, D.sideB.trans he⟩

/-- The full quadratic-and-quartic slack formula of the normalized theorem. -/
theorem slack_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.sideA + D.triangle.sideB - 1 =
      D.y ^ 2 / (2 * D.x * (1 - D.x)) -
        D.y ^ 4 / 8 * (1 / D.x ^ 3 + 1 / (1 - D.x) ^ 3) + D.y ^ 6 * E := by
  obtain ⟨E, hE, he⟩ := D.sideA_expansion
  obtain ⟨F, hF, hf⟩ := D.sideB_expansion
  refine ⟨E + F, SignSequence.finite_add hE hF, ?_⟩
  rw [he, hf]
  field_simp [D.x_pos.ne', D.complement_pos.ne']
  ring

/-- The slack's leading quadratic term retains a finite fourth-order remainder. -/
theorem slack_quadratic_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    D.triangle.sideA + D.triangle.sideB - 1 =
      D.y ^ 2 / (2 * D.x * (1 - D.x)) + D.y ^ 4 * E := by
  obtain ⟨E, hE, he⟩ := D.sideA_quadratic_expansion
  obtain ⟨F, hF, hf⟩ := D.sideB_quadratic_expansion
  refine ⟨E + F, SignSequence.finite_add hE hF, ?_⟩
  rw [he, hf]
  field_simp [D.x_pos.ne', D.complement_pos.ne']
  ring

end
end NormalizedFlatTriangle
end Surreal.Surcomplex
