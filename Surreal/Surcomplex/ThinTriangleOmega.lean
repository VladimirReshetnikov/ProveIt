import Surreal.Surcomplex.ThinTriangle
import Surreal.Foundations.SignSequenceStandardPartTopology
import Surreal.Surcomplex.InverseTrigonometricTaylor

/-!
# A thin triangle with infinite base and ordinary height

The first explicit family in `trigonometry:ex:hierarchies` has vertices
`0`, `omega`, and `omega/2+i`. Its actual area and circumradius are infinite,
its inradius is finite, and both base angles are infinitesimal.
-/

universe u

namespace Surreal.Surcomplex.ThinTriangleOmega

open Foundations

noncomputable section

/-- The actual first infinite ordinal, with no monomial convention imposed. -/
abbrev omega : SignSequence.{u} := SignSequence.ofOrdinal Ordinal.omega0

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

private theorem slope_infinitesimal : SignSequence.IsInfinitesimal (2 / omega.{u}) := by
  rw [div_eq_mul_inv]
  exact SignSequence.finite_mul_infinitesimal finite_two SignSequence.infinitesimal_inv_omega0

/-- Unit height is infinitesimal relative to both halves of the infinite base. -/
def data : ThinTriangle.{u} where
  L := omega
  x := omega / 2
  h := 1
  x_pos := div_pos SignSequence.omega0_pos (by norm_num)
  x_lt_base := by linarith only [SignSequence.omega0_pos.{u}]
  height_pos := zero_lt_one
  slope_left_infinitesimal := by
    have he : (1 : SignSequence.{u}) / (omega / 2) = 2 / omega := by ring
    rw [he]
    exact slope_infinitesimal
  slope_right_infinitesimal := by
    have he : (1 : SignSequence.{u}) / (omega - omega / 2) = 2 / omega := by ring
    rw [he]
    exact slope_infinitesimal

/-- The actual coordinate triangle of the first hierarchy example. -/
def triangle : Triangle.{u} := data.triangle

@[simp] theorem vertexA : triangle.{u}.A = 0 := rfl
@[simp] theorem vertexB : triangle.{u}.B = ofReal omega.{u} := rfl
@[simp] theorem vertexC : triangle.{u}.C = ⟨omega.{u} / 2, 1⟩ := rfl

/-- Both base angles have the exact source slope. -/
theorem angleA : triangle.{u}.angleA = arctan (2 / omega.{u}) := by
  rw [triangle, data.angleA]
  congr 1
  change (1 : SignSequence.{u}) / (omega / 2) = 2 / omega
  ring

theorem angleB : triangle.{u}.angleB = arctan (2 / omega.{u}) := by
  rw [triangle, data.angleB]
  congr 1
  change (1 : SignSequence.{u}) / (omega - omega / 2) = 2 / omega
  ring

/-- The area is exactly one half of the infinite base. -/
theorem area : triangle.{u}.area = omega.{u} / 2 := by
  simpa only [triangle, data, mul_one] using data.{u}.area

/-- The exact inverse-tangent expansion refines the source's first two displayed terms. -/
theorem angleA_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    triangle.{u}.angleA.val = 2 / omega.{u} - 8 / (3 * omega.{u} ^ 3) +
      32 / (5 * omega.{u} ^ 5) + (omega.{u}⁻¹) ^ 7 * E := by
  obtain ⟨E, hE, _, he⟩ := arctanFunction_expansion (2 / omega.{u}) slope_infinitesimal
  have hc : SignSequence.IsFinite (128 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (128 : ℝ)
  refine ⟨128 * E, SignSequence.finite_mul hc hE, ?_⟩
  rw [angleA]
  change arctanFunction (2 / omega.{u}) = _
  rw [he]
  field_simp [SignSequence.omega0_pos.ne']
  ring

/-- The ellipsis is the full actual strongly summable odd-power inverse-tangent series. -/
theorem angleA_eq_strongSum : triangle.{u}.angleA.val =
    SignSequence.strongSum (fun n : ℕ =>
      SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1)) * (2 / omega.{u}) ^ (2 * n + 1))
      (stronglySummable_arctanTaylor (2 / omega.{u}) slope_infinitesimal) := by
  rw [angleA]
  exact arctanFunction_eq_strongSum _ slope_infinitesimal

theorem base_angles_infinitesimal :
    SignSequence.IsInfinitesimal triangle.{u}.angleA.val ∧
      SignSequence.IsInfinitesimal triangle.{u}.angleB.val :=
  ⟨data.angleA_infinitesimal, data.angleB_infinitesimal⟩

/-- The circumradius is relatively equivalent to omega squared divided by eight. -/
theorem circumradius_asymptotic : SignSequence.IsInfinitesimal
    (triangle.{u}.circumradius / (omega.{u} ^ 2 / 8) - 1) := by
  have he := data.{u}.circumradius_asymptotic
  change SignSequence.IsInfinitesimal
    (triangle.{u}.circumradius / ((omega.{u} / 2) * (omega.{u} - omega.{u} / 2) / (2 * 1)) - 1) at he
  have hs : (omega.{u} / 2) * (omega.{u} - omega.{u} / 2) / (2 * 1) = omega.{u} ^ 2 / 8 := by ring
  rwa [hs] at he

/-- The actual inradius is infinitesimally close in relative error to one half. -/
theorem inradius_asymptotic : SignSequence.IsInfinitesimal
    (triangle.{u}.inradius / (1 / 2) - 1) := data.inradius_asymptotic

/-- The area is infinite. -/
theorem area_not_finite : ¬ SignSequence.IsFinite triangle.{u}.area := by
  rw [area]
  apply (SignSequence.infinitesimal_inv_iff_not_finite
    (div_ne_zero SignSequence.omega0_pos.ne' (by norm_num))).mp
  rw [inv_div]
  exact slope_infinitesimal

private theorem radius_scale_not_finite : ¬ SignSequence.IsFinite (omega.{u} ^ 2 / 8) := by
  apply (SignSequence.infinitesimal_inv_iff_not_finite
    (div_ne_zero (pow_ne_zero 2 SignSequence.omega0_pos.ne') (by norm_num))).mp
  rw [inv_div, div_eq_mul_inv, ← inv_pow]
  have hc : SignSequence.IsFinite (8 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (8 : ℝ)
  exact SignSequence.finite_mul_infinitesimal hc
    ((SignSequence.infinitesimal_sq_iff _).mpr SignSequence.infinitesimal_inv_omega0)

/-- The actual circumradius is infinite. -/
theorem circumradius_not_finite : ¬ SignSequence.IsFinite triangle.{u}.circumradius := by
  exact radius_scale_not_finite ∘
    (SignSequence.finite_iff_of_infinitesimal_div_sub_one
      (div_ne_zero (pow_ne_zero 2 SignSequence.omega0_pos.ne') (by norm_num))
      circumradius_asymptotic.{u}).mp

/-- The actual inradius has ordinary finite scale. -/
theorem inradius_finite : SignSequence.IsFinite triangle.{u}.inradius := by
  apply (SignSequence.finite_iff_of_infinitesimal_div_sub_one
    (by norm_num : (1 / 2 : SignSequence.{u}) ≠ 0) inradius_asymptotic).mpr
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)

end
end Surreal.Surcomplex.ThinTriangleOmega
