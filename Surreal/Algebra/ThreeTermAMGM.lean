import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Three-term arithmetic-geometric mean over an ordered field

The cubic inequality and its equality case use only ordered-field
algebra, so they apply to arbitrary surreal scales. They supply the
algebraic inequality in `trigonometry:cor:areabound`.
-/

namespace Surreal

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

private theorem three_term_cubic_amgm_least (x y z : F) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hxz : x ≤ z) :
    27 * x * y * z ≤ (x + y + z) ^ 3 ∧
      (27 * x * y * z = (x + y + z) ^ 3 ↔ x = y ∧ y = z) := by
  have hid : (x + y + z) ^ 3 - 27 * x * y * z =
      9 * x * ((y - z) ^ 2 + (y - x) * (z - x)) + (y + z - 2 * x) ^ 3 := by ring
  have hbase : 0 ≤ y + z - 2 * x := by linarith only [hxy, hxz]
  have hterm : 0 ≤ 9 * x * ((y - z) ^ 2 + (y - x) * (z - x)) :=
    mul_nonneg (mul_nonneg (by norm_num) hx)
      (add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxz)))
  have hcube : 0 ≤ (y + z - 2 * x) ^ 3 := pow_nonneg hbase 3
  refine ⟨by linarith only [hid, hterm, hcube], ?_⟩
  constructor
  · intro he
    have hz : (y + z - 2 * x) ^ 3 = 0 := by linarith only [hid, hterm, hcube, he]
    have hzero := eq_zero_of_pow_eq_zero hz
    exact ⟨by linarith only [hxy, hxz, hzero], by linarith only [hxy, hxz, hzero]⟩
  · rintro ⟨rfl, rfl⟩
    ring

/-- Cubic three-term AM-GM holds over any ordered field, including non-Archimedean fields. -/
theorem three_term_cubic_amgm (x y z : F) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * x * y * z ≤ (x + y + z) ^ 3 := by
  rcases le_total x y with hxy | hyx
  · rcases le_total x z with hxz | hzx
    · exact (three_term_cubic_amgm_least x y z hx hxy hxz).1
    · have he := (three_term_cubic_amgm_least z x y hz hzx (hzx.trans hxy)).1
      nlinarith only [he]
  · rcases le_total y z with hyz | hzy
    · have he := (three_term_cubic_amgm_least y x z hy hyx hyz).1
      nlinarith only [he]
    · have he := (three_term_cubic_amgm_least z x y hz (hzy.trans hyx) hzy).1
      nlinarith only [he]

/-- Equality in cubic three-term AM-GM holds exactly when all three nonnegative terms agree. -/
theorem three_term_cubic_amgm_eq_iff (x y z : F) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * x * y * z = (x + y + z) ^ 3 ↔ x = y ∧ y = z := by
  constructor
  · intro he
    rcases le_total x y with hxy | hyx
    · rcases le_total x z with hxz | hzx
      · exact (three_term_cubic_amgm_least x y z hx hxy hxz).2.mp he
      · have hh := (three_term_cubic_amgm_least z x y hz hzx (hzx.trans hxy)).2.mp
          (by nlinarith only [he])
        exact ⟨hh.2, hh.2.symm.trans hh.1.symm⟩
    · rcases le_total y z with hyz | hzy
      · have hh := (three_term_cubic_amgm_least y x z hy hyx hyz).2.mp
          (by nlinarith only [he])
        exact ⟨hh.1.symm, hh.1.trans hh.2⟩
      · have hh := (three_term_cubic_amgm_least z x y hz (hzy.trans hyx) hzy).2.mp
          (by nlinarith only [he])
        exact ⟨hh.2, hh.2.symm.trans hh.1.symm⟩
  · rintro ⟨rfl, rfl⟩
    ring

end Surreal
