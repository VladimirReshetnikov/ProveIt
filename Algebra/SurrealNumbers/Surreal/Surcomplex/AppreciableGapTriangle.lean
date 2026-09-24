import Surreal.Surcomplex.TriangleFromSides
import Surreal.Surcomplex.TriangleFlatAsymptotics
import Surreal.Foundations.SignSequenceStandardPartTopology

/-!
# A flat triangle whose side gap is appreciable

The actual ordinal omega realizes `trigonometry:ex:appreciablegap` with
sides `2*omega^2-1, omega^2, omega^2`. Its gap is exactly one, but the relative
gap is infinitesimal. The angle, area and circumradius have the source's
literal equivalents; both area and circumradius are infinite.
-/

universe u

namespace Surreal.Surcomplex.AppreciableGapTriangle

open Foundations

noncomputable section

/-- The actual first infinite ordinal in the surreal field. -/
abbrev omega : SignSequence.{u} := SignSequence.ofOrdinal Ordinal.omega0

private theorem omega_gt_one : 1 < omega.{u} := by
  simpa only [Nat.cast_one] using SignSequence.natCast_lt_omega0.{u} 1

private theorem omega_sq_gt_one : 1 < omega.{u} ^ 2 := by
  nlinarith only [omega_gt_one, sq_nonneg (omega.{u} - 1)]

private theorem exists_triangle : ∃ T : Triangle.{u},
    T.sideA = 2 * omega.{u} ^ 2 - 1 ∧ T.sideB = omega.{u} ^ 2 ∧ T.sideC = omega.{u} ^ 2 := by
  have hw : 0 < omega.{u} ^ 2 := sq_pos_of_pos SignSequence.omega0_pos
  have ha : 0 < 2 * omega.{u} ^ 2 - 1 := by linarith only [omega_sq_gt_one]
  apply (exists_triangle_sides_iff _ _ _ ha hw hw).mpr
  constructor
  · linarith
  constructor <;> linarith

/-- An actual noncollinear triangle with the prescribed infinite sides. -/
def triangle : Triangle.{u} := Classical.choose exists_triangle

@[simp] theorem sideA : triangle.{u}.sideA = 2 * omega.{u} ^ 2 - 1 :=
  (Classical.choose_spec exists_triangle).1

@[simp] theorem sideB : triangle.{u}.sideB = omega.{u} ^ 2 :=
  (Classical.choose_spec exists_triangle).2.1

@[simp] theorem sideC : triangle.{u}.sideC = omega.{u} ^ 2 :=
  (Classical.choose_spec exists_triangle).2.2

theorem sideA_largest : triangle.{u}.sideB ≤ triangle.{u}.sideA ∧
    triangle.{u}.sideC ≤ triangle.{u}.sideA := by
  rw [sideA, sideB, sideC]
  constructor <;> linarith only [omega_sq_gt_one]

/-- The unnormalized triangle-inequality gap is exactly the ordinary number one. -/
@[simp] theorem sideGap : triangle.{u}.sideGap = 1 := by
  rw [Triangle.sideGap, sideA, sideB, sideC]
  ring

/-- The effective length scale is omega squared divided by two. -/
theorem effective_length : triangle.{u}.sideB * triangle.{u}.sideC /
    (triangle.{u}.sideB + triangle.{u}.sideC) = omega.{u} ^ 2 / 2 := by
  rw [sideB, sideC]
  field_simp [SignSequence.omega0_pos.ne']
  ring

/-- The relative gap is twice the inverse square of omega. -/
theorem relativeGap : triangle.{u}.relativeGap = 2 / omega.{u} ^ 2 := by
  rw [Triangle.relativeGap, sideGap, effective_length]
  ring

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

/-- The gap satisfies the relative threshold despite being appreciable. -/
theorem relativeGap_infinitesimal : SignSequence.IsInfinitesimal triangle.{u}.relativeGap := by
  rw [relativeGap, div_eq_mul_inv, ← inv_pow]
  exact SignSequence.finite_mul_infinitesimal finite_two
    ((SignSequence.infinitesimal_sq_iff _).mpr SignSequence.infinitesimal_inv_omega0)

/-- The largest angle is infinitesimally below pi. -/
theorem supplement_infinitesimal : SignSequence.IsInfinitesimal triangle.{u}.angleSupplement.val :=
  (triangle.{u}.infinitesimal_angleSupplement_iff_relativeGap
    sideA_largest.{u}.1 sideA_largest.{u}.2).mpr relativeGap_infinitesimal

/-- The source's angle equivalent is literally two divided by the actual ordinal omega. -/
theorem supplement_asymptotic : SignSequence.IsInfinitesimal
    (triangle.{u}.angleSupplement.val / (2 / omega.{u}) - 1) := by
  have he := triangle.{u}.flat_supplement_asymptotic
    sideA_largest.{u}.1 sideA_largest.{u}.2 relativeGap_infinitesimal
  rw [sideB, sideC, sideGap] at he
  have hs : SignSequence.sqrt (2 * (omega.{u} ^ 2 + omega.{u} ^ 2) * 1 / (omega.{u} ^ 2 * omega.{u} ^ 2)) = 2 / omega.{u} := by
    apply SignSequence.sqrt_eq_of_nonneg_sq (div_pos (by norm_num) SignSequence.omega0_pos).le
    field_simp [SignSequence.omega0_pos.ne']
    ring
  rwa [hs] at he

/-- The area is algebraically equivalent to omega cubed. -/
theorem area_asymptotic : SignSequence.IsInfinitesimal (triangle.{u}.area / omega.{u} ^ 3 - 1) := by
  have he := triangle.{u}.flat_area_asymptotic
    sideA_largest.{u}.1 sideA_largest.{u}.2 relativeGap_infinitesimal
  rw [sideB, sideC, sideGap] at he
  have hs : SignSequence.sqrt (omega.{u} ^ 2 * omega.{u} ^ 2 * (omega.{u} ^ 2 + omega.{u} ^ 2) * 1 / 2) = omega.{u} ^ 3 := by
    apply SignSequence.sqrt_eq_of_nonneg_sq (pow_pos SignSequence.omega0_pos 3).le
    ring
  rwa [hs] at he

/-- The circumradius is algebraically equivalent to one half of omega cubed. -/
theorem circumradius_asymptotic : SignSequence.IsInfinitesimal
    (triangle.{u}.circumradius / (omega.{u} ^ 3 / 2) - 1) := by
  have he := triangle.{u}.flat_circumradius_asymptotic
    sideA_largest.{u}.1 sideA_largest.{u}.2 relativeGap_infinitesimal
  rw [sideB, sideC, sideGap] at he
  have hs : SignSequence.sqrt ((omega.{u} ^ 2 + omega.{u} ^ 2) * omega.{u} ^ 2 * omega.{u} ^ 2 / (8 * 1)) = omega.{u} ^ 3 / 2 := by
    apply SignSequence.sqrt_eq_of_nonneg_sq
      (div_pos (pow_pos SignSequence.omega0_pos 3) (by norm_num)).le
    ring
  rwa [hs] at he

private theorem inverse_cube_infinitesimal : SignSequence.IsInfinitesimal ((omega.{u} ^ 3)⁻¹) := by
  rw [← inv_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
  exact SignSequence.finite_mul_infinitesimal
    (SignSequence.finite_pow (SignSequence.finite_of_infinitesimal
      SignSequence.infinitesimal_inv_omega0) 2) SignSequence.infinitesimal_inv_omega0

private theorem cube_not_finite : ¬ SignSequence.IsFinite (omega.{u} ^ 3) :=
  (SignSequence.infinitesimal_inv_iff_not_finite
    (pow_ne_zero 3 SignSequence.omega0_pos.ne')).mp inverse_cube_infinitesimal

private theorem half_cube_not_finite : ¬ SignSequence.IsFinite (omega.{u} ^ 3 / 2) := by
  apply (SignSequence.infinitesimal_inv_iff_not_finite
    (div_ne_zero (pow_ne_zero 3 SignSequence.omega0_pos.ne') (by norm_num))).mp
  rw [inv_div, div_eq_mul_inv]
  exact SignSequence.finite_mul_infinitesimal finite_two inverse_cube_infinitesimal

/-- The nearly flat triangle has infinite area, despite its ordinary side gap. -/
theorem area_not_finite : ¬ SignSequence.IsFinite triangle.{u}.area := by
  have hv := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (pow_ne_zero 3 SignSequence.omega0_pos.ne') area_asymptotic.{u}
  rw [SignSequence.isFinite_iff_valuation_nonneg, hv]
  exact cube_not_finite ∘ (SignSequence.isFinite_iff_valuation_nonneg _).mpr

/-- The actual circumradius is infinite as well. -/
theorem circumradius_not_finite : ¬ SignSequence.IsFinite triangle.{u}.circumradius := by
  have hv := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (div_ne_zero (pow_ne_zero 3 SignSequence.omega0_pos.ne') (by norm_num))
    circumradius_asymptotic.{u}
  rw [SignSequence.isFinite_iff_valuation_nonneg, hv]
  exact half_cube_not_finite ∘ (SignSequence.isFinite_iff_valuation_nonneg _).mpr

end
end Surreal.Surcomplex.AppreciableGapTriangle
