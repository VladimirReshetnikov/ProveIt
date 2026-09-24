import Surreal.Algebra.ThreeTermAMGM
import Surreal.Surcomplex.TriangleHeron

/-!
# The sharp triangle area bound at arbitrary surreal scales

Apply ordered-field three-term AM-GM to the three positive side defects
in Heron's formula. This proves `trigonometry:cor:areabound`, including
its equality characterization by equal actual side lengths.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The three positive side defects sum to the semiperimeter. -/
theorem side_defects_sum (T : Triangle.{u}) :
    (T.semiperimeter - T.sideA) + (T.semiperimeter - T.sideB) +
      (T.semiperimeter - T.sideC) = T.semiperimeter := by
  dsimp only [semiperimeter]
  ring

/-- The polynomial form of the sharp area bound, without square-root denominators. -/
theorem area_sq_bound (T : Triangle.{u}) : 27 * T.area ^ 2 ≤ T.semiperimeter ^ 4 := by
  have he := three_term_cubic_amgm
    (T.semiperimeter - T.sideA) (T.semiperimeter - T.sideB) (T.semiperimeter - T.sideC)
    T.semiperimeter_sub_sideA_pos.le T.semiperimeter_sub_sideB_pos.le
    T.semiperimeter_sub_sideC_pos.le
  rw [T.side_defects_sum] at he
  calc
    _ = T.semiperimeter * (27 * (T.semiperimeter - T.sideA) *
        (T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC)) := by rw [T.heron]; ring
    _ ≤ T.semiperimeter * T.semiperimeter ^ 3 :=
      mul_le_mul_of_nonneg_left he T.semiperimeter_pos.le
    _ = _ := by ring

/-- Equality in the polynomial area bound characterizes equal actual side lengths. -/
theorem area_sq_bound_eq_iff (T : Triangle.{u}) :
    27 * T.area ^ 2 = T.semiperimeter ^ 4 ↔
      T.sideA = T.sideB ∧ T.sideB = T.sideC := by
  constructor
  · intro he
    have hmul : T.semiperimeter * (27 * (T.semiperimeter - T.sideA) *
        (T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC)) =
        T.semiperimeter * T.semiperimeter ^ 3 := by
      rw [T.heron] at he
      nlinarith only [he]
    have hp := mul_left_cancel₀ T.semiperimeter_pos.ne' hmul
    have hh := (three_term_cubic_amgm_eq_iff
      (T.semiperimeter - T.sideA) (T.semiperimeter - T.sideB) (T.semiperimeter - T.sideC)
      T.semiperimeter_sub_sideA_pos.le T.semiperimeter_sub_sideB_pos.le
      T.semiperimeter_sub_sideC_pos.le).mp (by rwa [T.side_defects_sum])
    exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  · rintro ⟨hab, hbc⟩
    rw [T.heron]
    dsimp only [semiperimeter]
    rw [hab, hbc]
    ring

/-- The exact scale-independent area bound from the trigonometry report. -/
theorem area_le_semiperimeter_sq (T : Triangle.{u}) :
    T.area ≤ T.semiperimeter ^ 2 / (3 * SignSequence.sqrt 3) := by
  have hd : 0 < 3 * SignSequence.sqrt (3 : SignSequence.{u}) :=
    mul_pos (by norm_num) (SignSequence.sqrt_pos (by norm_num))
  apply (sq_le_sq₀ T.area_pos.le (div_nonneg (sq_nonneg _) hd.le)).mp
  calc
    T.area ^ 2 ≤ T.semiperimeter ^ 4 / 27 :=
      (le_div_iff₀ (by norm_num : (0 : SignSequence.{u}) < 27)).mpr
        (by nlinarith only [T.area_sq_bound])
    _ = (T.semiperimeter ^ 2 / (3 * SignSequence.sqrt 3)) ^ 2 := by
      rw [div_pow, mul_pow, SignSequence.sqrt_sq (by norm_num : (0 : SignSequence.{u}) ≤ 3)]
      ring

/-- Equality in the sharp area bound holds exactly for equilateral triangles. -/
theorem area_eq_semiperimeter_sq_iff (T : Triangle.{u}) :
    T.area = T.semiperimeter ^ 2 / (3 * SignSequence.sqrt 3) ↔
      T.sideA = T.sideB ∧ T.sideB = T.sideC := by
  have hd : 0 < 3 * SignSequence.sqrt (3 : SignSequence.{u}) :=
    mul_pos (by norm_num) (SignSequence.sqrt_pos (by norm_num))
  have hs : (T.semiperimeter ^ 2 / (3 * SignSequence.sqrt 3)) ^ 2 =
      T.semiperimeter ^ 4 / 27 := by
    rw [div_pow, mul_pow, SignSequence.sqrt_sq (by norm_num : (0 : SignSequence.{u}) ≤ 3)]
    ring
  constructor
  · intro he
    apply T.area_sq_bound_eq_iff.mp
    rw [he, hs]
    ring
  · intro he
    apply (sq_eq_sq₀ T.area_pos.le (div_nonneg (sq_nonneg _) hd.le)).mp
    rw [hs]
    have hpoly := T.area_sq_bound_eq_iff.mpr he
    apply (eq_div_iff (by norm_num : (27 : SignSequence.{u}) ≠ 0)).mpr
    nlinarith only [hpoly]

end
end Surreal.Surcomplex.Triangle
