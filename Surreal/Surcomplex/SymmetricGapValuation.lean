import Surreal.Surcomplex.SymmetricGapTriangle
import Surreal.Surcomplex.SymmetricGapSeries
import Surreal.Surcomplex.TriangleFlatAsymptotics
import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# Square-root scales in the symmetric side-gap example

The three complete strong series and final scale assertions of `trigonometry:ex:flatgap`
concern the actual constructed triangle. All three sides have valuation zero. Its positive
altitude and area have half the gap's valuation and are infinitesimal, while its circumradius
is infinite. The angle supplement is relatively equivalent to twice the square root of the gap.
-/

universe u

namespace Surreal.Surcomplex.SymmetricGapTriangle

open Foundations

local notation "v" => SignSequence.valuation

variable (D : SymmetricGapTriangle.{u})

/-- The actual angle supplement has the complete strongly summable series from the example. -/
theorem supplement_eq_strongSum :
    D.triangle.angleSupplement.val / (2 * SignSequence.sqrt D.τ) =
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (16 ^ n * (2 * n + 1))) * D.τ ^ n)
        (stronglySummable_symmetricGapAngle D.τ D.τ_infinitesimal) := by
  rw [D.angleSupplement_eq]
  exact symmetricGap_angle_eq_strongSum D.τ D.τ_pos D.τ_infinitesimal

/-- The actual altitude has the complete binomial strong series at its square-root scale. -/
theorem height_eq_strongSum :
    D.height / SignSequence.sqrt D.τ =
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal (Ring.choose (1 / 2 : ℝ) n * (-1 / 4) ^ n) * D.τ ^ n)
        (stronglySummable_symmetricGapHeight D.τ D.τ_infinitesimal) :=
  symmetricGap_height_eq_strongSum D.τ D.τ_pos D.τ_infinitesimal

/-- The actual circumradius has the complete inverse-binomial strong series. -/
theorem circumradius_eq_strongSum :
    D.triangle.circumradius * (2 * SignSequence.sqrt D.τ) =
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal (Ring.choose (-1 / 2 : ℝ) n * (-1 / 4) ^ n) * D.τ ^ n)
        (stronglySummable_symmetricGapRadius D.τ D.τ_infinitesimal) := by
  rw [D.circumradius]
  exact symmetricGap_radius_eq_strongSum D.τ D.τ_pos D.τ_infinitesimal

/-- The displayed cubic supplement bracket retains an exact finite fourth-order tail. -/
theorem supplement_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    SignSequence.standardPart E = 35 / 294912 ∧
    D.triangle.angleSupplement.val / (2 * SignSequence.sqrt D.τ) =
      1 + D.τ / 24 + 3 * D.τ ^ 2 / 640 + 5 * D.τ ^ 3 / 7168 + D.τ ^ 4 * E := by
  rw [D.angleSupplement_eq]
  exact symmetricGap_angle_expansion D.τ D.τ_pos D.τ_infinitesimal

/-- The displayed cubic altitude bracket applies to the actual perpendicular distance. -/
theorem height_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    SignSequence.standardPart E = -5 / 32768 ∧
    D.height / SignSequence.sqrt D.τ =
      1 - D.τ / 8 - D.τ ^ 2 / 128 - D.τ ^ 3 / 1024 + D.τ ^ 4 * E :=
  symmetricGap_height_expansion D.τ D.τ_pos D.τ_infinitesimal

/-- The displayed cubic circumradius bracket retains the next ordinary coefficient in its tail. -/
theorem circumradius_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    SignSequence.standardPart E = 35 / 32768 ∧
    D.triangle.circumradius * (2 * SignSequence.sqrt D.τ) =
      1 + D.τ / 8 + 3 * D.τ ^ 2 / 128 + 5 * D.τ ^ 3 / 1024 + D.τ ^ 4 * E := by
  rw [D.circumradius]
  exact symmetricGap_radius_expansion D.τ D.τ_pos D.τ_infinitesimal

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

private theorem standardPart_two : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
  simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)

private theorem valuation_two : v (2 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using
    (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0) :
      v (SignSequence.ofReal 2 : SignSequence.{u}) = 0)

private theorem gap_half_infinitesimal : SignSequence.IsInfinitesimal (D.τ / 2) := by
  apply SignSequence.infinitesimal_of_abs_le (y := D.τ) _ D.τ_infinitesimal
  rw [abs_of_pos D.τ_pos, abs_of_pos (div_pos D.τ_pos (by norm_num))]
  linarith only [D.τ_pos]

private theorem gap_quarter_infinitesimal : SignSequence.IsInfinitesimal (D.τ / 4) := by
  apply SignSequence.infinitesimal_of_abs_le (y := D.τ) _ D.τ_infinitesimal
  rw [abs_of_pos D.τ_pos, abs_of_pos (div_pos D.τ_pos (by norm_num))]
  linarith only [D.τ_pos]

private theorem area_factor_infinitesimal :
    SignSequence.IsInfinitesimal ((1 - D.τ / 2) - 1) := by
  simpa only [sub_sub_cancel_left] using SignSequence.infinitesimal_neg D.gap_half_infinitesimal

/-- Every side retains ordinary scale although the triangle becomes angularly flat. -/
theorem valuation_sides :
    v D.triangle.sideA = 0 ∧ v D.triangle.sideB = 0 ∧ v D.triangle.sideC = 0 := by
  have hτ := SignSequence.finite_of_infinitesimal D.τ_infinitesimal
  have hs : SignSequence.standardPart (2 - D.τ) = 2 := by
    rw [SignSequence.standardPart_sub finite_two hτ, standardPart_two,
      (SignSequence.standardPart_eq_zero_iff hτ).mpr D.τ_infinitesimal, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [D.sideA]
    apply (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero
      (SignSequence.finite_sub finite_two hτ)).mpr
    rw [hs]
    norm_num
  · rw [D.sideB, SignSequence.valuation_one]
  · rw [D.sideC, SignSequence.valuation_one]

/-- The actual altitude is relatively equivalent to the positive square root of the side gap. -/
theorem height_asymptotic :
    SignSequence.IsInfinitesimal (D.height / SignSequence.sqrt D.τ - 1) := by
  apply SignSequence.infinitesimal_sub_one_of_sq_sub_one
    (div_nonneg D.height_pos.le (SignSequence.sqrt_nonneg _))
  have he : (D.height / SignSequence.sqrt D.τ) ^ 2 - 1 = -(D.τ / 4) := by
    rw [div_pow, D.height_sq, SignSequence.sqrt_sq D.τ_pos.le]
    field_simp [D.τ_pos.ne']
    ring
  rw [he]
  exact SignSequence.infinitesimal_neg D.gap_quarter_infinitesimal

/-- A square-root altitude has precisely the square-root valuation, including its finite exponent. -/
theorem valuation_height : v D.height = v (SignSequence.sqrt D.τ) :=
  SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (SignSequence.sqrt_pos D.τ_pos).ne' D.height_asymptotic

/-- Intrinsic doubled-valuation form of the square-root height scale. -/
theorem two_nsmul_valuation_height : 2 • v D.height = v D.τ := by
  rw [D.valuation_height, ← SignSequence.valuation.map_pow,
    SignSequence.sqrt_sq D.τ_pos.le]

/-- The altitude is a nonzero infinitesimal actual distance to the opposite side's line. -/
theorem height_infinitesimal : SignSequence.IsInfinitesimal D.height := by
  have hf := SignSequence.finite_of_infinitesimal_sub_one D.height_asymptotic
  have hi := SignSequence.infinitesimal_sqrt D.τ_pos.le D.τ_infinitesimal
  simpa only [div_mul_cancel₀ _ (SignSequence.sqrt_pos D.τ_pos).ne'] using
    SignSequence.finite_mul_infinitesimal hf hi

/-- The finite area factor has residue one and cannot change the altitude's valuation. -/
theorem valuation_area : v D.triangle.area = v D.height := by
  rw [D.area, SignSequence.valuation_mul,
    SignSequence.valuation_eq_zero_of_infinitesimal_sub_one D.area_factor_infinitesimal,
    zero_add]

theorem two_nsmul_valuation_area : 2 • v D.triangle.area = v D.τ := by
  rw [D.valuation_area, D.two_nsmul_valuation_height]

/-- The positive actual area is infinitesimal, despite all three sides having ordinary scale. -/
theorem area_infinitesimal : SignSequence.IsInfinitesimal D.triangle.area := by
  rw [D.area]
  exact SignSequence.finite_mul_infinitesimal
    (SignSequence.finite_of_infinitesimal_sub_one D.area_factor_infinitesimal)
    D.height_infinitesimal

/-- The area has the same positive leading equivalent as the altitude. -/
theorem area_asymptotic :
    SignSequence.IsInfinitesimal (D.triangle.area / SignSequence.sqrt D.τ - 1) := by
  rw [D.area, mul_div_assoc]
  exact SignSequence.infinitesimal_mul_sub_one D.area_factor_infinitesimal D.height_asymptotic

/-- The circumradius has the reciprocal square-root valuation. -/
theorem valuation_circumradius : v D.triangle.circumradius = -v D.height := by
  rw [D.circumradius, SignSequence.valuation_div, SignSequence.valuation_one,
    SignSequence.valuation_mul, valuation_two, zero_add, zero_sub]

/-- The circumradius's reciprocal is a positive infinitesimal, so the radius is infinite. -/
theorem circumradius_not_finite : ¬ SignSequence.IsFinite D.triangle.circumradius := by
  apply (SignSequence.infinitesimal_inv_iff_not_finite D.triangle.circumradius_pos.ne').mp
  rw [D.circumradius, one_div, inv_inv]
  exact SignSequence.finite_mul_infinitesimal finite_two D.height_infinitesimal

/-- The actual circumradius is relatively equivalent to the reciprocal of twice the square root. -/
theorem circumradius_asymptotic :
    SignSequence.IsInfinitesimal
      (D.triangle.circumradius / (1 / (2 * SignSequence.sqrt D.τ)) - 1) := by
  have he : D.triangle.circumradius / (1 / (2 * SignSequence.sqrt D.τ)) =
      (D.height / SignSequence.sqrt D.τ)⁻¹ := by
    rw [D.circumradius]
    field_simp [D.height_pos.ne', (SignSequence.sqrt_pos D.τ_pos).ne']
  rw [he]
  exact SignSequence.infinitesimal_inv_sub_one D.height_asymptotic

private theorem relativeGap_infinitesimal :
    SignSequence.IsInfinitesimal D.triangle.relativeGap := by
  have he : D.triangle.relativeGap = 2 * D.τ := by
    unfold Triangle.relativeGap
    rw [D.sideGap, D.sideB, D.sideC]
    ring
  rw [he]
  exact SignSequence.finite_mul_infinitesimal finite_two D.τ_infinitesimal

/-- The angle supplement has exactly the leading square-root equivalent displayed in the example. -/
theorem supplement_asymptotic :
    SignSequence.IsInfinitesimal
      (D.triangle.angleSupplement.val / (2 * SignSequence.sqrt D.τ) - 1) := by
  have he : SignSequence.sqrt (2 * (1 + 1) * D.τ / (1 * 1)) =
      2 * SignSequence.sqrt D.τ := by
    apply SignSequence.sqrt_eq_of_nonneg_sq
      (mul_nonneg (by norm_num) (SignSequence.sqrt_nonneg _))
    rw [mul_pow, SignSequence.sqrt_sq D.τ_pos.le]
    ring
  have h := D.triangle.flat_supplement_asymptotic
    D.sideA_largest.1 D.sideA_largest.2 D.relativeGap_infinitesimal
  rwa [D.sideB, D.sideC, D.sideGap, he] at h

/-- The infinitesimal supplement has the same valuation as the altitude. -/
theorem valuation_supplement : v D.triangle.angleSupplement.val = v D.height := by
  have h := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (mul_ne_zero (by norm_num : (2 : SignSequence.{u}) ≠ 0)
      (SignSequence.sqrt_pos D.τ_pos).ne') D.supplement_asymptotic
  rw [SignSequence.valuation_mul, valuation_two, zero_add, ← D.valuation_height] at h
  exact h

theorem supplement_infinitesimal : SignSequence.IsInfinitesimal D.triangle.angleSupplement.val :=
  (D.triangle.infinitesimal_angleSupplement_iff_relativeGap
    D.sideA_largest.1 D.sideA_largest.2).mpr D.relativeGap_infinitesimal

end Surreal.Surcomplex.SymmetricGapTriangle
