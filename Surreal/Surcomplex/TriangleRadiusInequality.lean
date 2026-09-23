import Surreal.Surcomplex.TriangleHeron

/-!
# Euler's radius inequality and its equality case

A positive sum of side-defect-weighted squares proves the radius
inequality in `trigonometry:thm:euler` for actual surcomplex triangles.
The exact equality condition is equilateral side data, with no
restriction on the surreal scales of the sides or radii.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The radius defect is an explicit sum of nonnegative weighted side differences. -/
theorem euler_radius_defect_squares (T : Triangle.{u}) :
    4 * T.area * (T.circumradius - 2 * T.inradius) =
      (T.semiperimeter - T.sideA) * (T.sideB - T.sideC) ^ 2 +
      (T.semiperimeter - T.sideB) * (T.sideC - T.sideA) ^ 2 +
      (T.semiperimeter - T.sideC) * (T.sideA - T.sideB) ^ 2 := by
  calc
    _ = T.sideA * T.sideB * T.sideC - 8 * T.area ^ 2 / T.semiperimeter := by
      rw [T.circumradius_eq_side_product, inradius]
      field_simp [T.area_pos.ne', T.semiperimeter_pos.ne']
      ring
    _ = T.sideA * T.sideB * T.sideC -
        8 * (T.semiperimeter - T.sideA) * (T.semiperimeter - T.sideB) *
          (T.semiperimeter - T.sideC) := by
      rw [T.heron]
      field_simp [T.semiperimeter_pos.ne']
    _ = _ := by
      dsimp [semiperimeter]
      ring

/-- Euler's inequality holds for the actual surreal-valued incircle and circumcircle radii. -/
theorem twice_inradius_le_circumradius (T : Triangle.{u}) :
    2 * T.inradius ≤ T.circumradius := by
  have hA := mul_nonneg T.semiperimeter_sub_sideA_pos.le
    (sq_nonneg (T.sideB - T.sideC))
  have hB := mul_nonneg T.semiperimeter_sub_sideB_pos.le
    (sq_nonneg (T.sideC - T.sideA))
  have hC := mul_nonneg T.semiperimeter_sub_sideC_pos.le
    (sq_nonneg (T.sideA - T.sideB))
  have h : 0 ≤ 4 * T.area * (T.circumradius - 2 * T.inradius) := by
    rw [T.euler_radius_defect_squares]
    exact add_nonneg (add_nonneg hA hB) hC
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left
    (mul_pos (by norm_num) T.area_pos)).mp h)

/-- Equality in Euler's radius inequality is equivalent to equal lengths of all three sides. -/
theorem circumradius_eq_twice_inradius_iff (T : Triangle.{u}) :
    T.circumradius = 2 * T.inradius ↔ T.sideA = T.sideB ∧ T.sideB = T.sideC := by
  constructor
  · intro he
    have hA := mul_nonneg T.semiperimeter_sub_sideA_pos.le
      (sq_nonneg (T.sideB - T.sideC))
    have hB := mul_nonneg T.semiperimeter_sub_sideB_pos.le
      (sq_nonneg (T.sideC - T.sideA))
    have hC := mul_nonneg T.semiperimeter_sub_sideC_pos.le
      (sq_nonneg (T.sideA - T.sideB))
    have hs := T.euler_radius_defect_squares
    rw [he, sub_self, mul_zero] at hs
    have hzA : (T.semiperimeter - T.sideA) * (T.sideB - T.sideC) ^ 2 = 0 := by
      linarith only [hs, hA, hB, hC]
    have hzC : (T.semiperimeter - T.sideC) * (T.sideA - T.sideB) ^ 2 = 0 := by
      linarith only [hs, hA, hB, hC]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hzC).resolve_left T.semiperimeter_sub_sideC_pos.ne')),
      sub_eq_zero.mp (sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hzA).resolve_left T.semiperimeter_sub_sideA_pos.ne'))⟩
  · rintro ⟨hAB, hBC⟩
    have hz : 4 * T.area * (T.circumradius - 2 * T.inradius) = 0 := by
      rw [T.euler_radius_defect_squares, hAB, hBC]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (by norm_num) T.area_pos.ne'))

/-- Every nonequilateral actual triangle has strictly larger circumradius than twice its inradius. -/
theorem twice_inradius_lt_circumradius (T : Triangle.{u})
    (h : ¬(T.sideA = T.sideB ∧ T.sideB = T.sideC)) :
    2 * T.inradius < T.circumradius := by
  rcases eq_or_lt_of_le T.twice_inradius_le_circumradius with he | hl
  · exact False.elim (h (T.circumradius_eq_twice_inradius_iff.mp he.symm))
  · exact hl

end
end Surreal.Surcomplex.Triangle
