import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Lean.Elab.Tactic.Omega

namespace NewAlgebraSimplifications

/-- A positive polynomial certificate replaces the norm cone contradiction. -/
theorem auxiliary_estimates {S V y : ℤ} (hS : 2 ≤ S)
    (hn : S ^ 2 * V ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1) :
    y ≠ 0 ∧ |y| < 2 * |V| := by
  have hS2 : 4 ≤ S ^ 2 := by nlinarith
  have hV : V ≠ 0 := by
    intro hV
    rw [hV] at hn
    have hm := mul_nonneg (by omega : 0 ≤ S ^ 2 - 1) (sq_nonneg y)
    norm_num at hn
    linarith
  have hV2 : 1 ≤ V ^ 2 := sq_pos_of_ne_zero hV
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hn
    have hm := mul_le_mul_of_nonneg_right hS2 (sq_nonneg V)
    norm_num at hn
    nlinarith
  refine ⟨hy, abs_lt_of_sq_lt_sq ?_ (by positivity)⟩
  have hnonneg := mul_nonneg (show 0 ≤ 3 * S ^ 2 - 4 by omega) (sq_nonneg V)
  have hprod : 0 < (S ^ 2 - 1) * (4 * V ^ 2 - y ^ 2) := by
    nlinarith only [hn, hnonneg]
  have hlt := pos_of_mul_pos_right hprod (show 0 ≤ S ^ 2 - 1 by omega)
  nlinarith only [hlt, sq_abs V]

/-- The affine carrier step dominates the entire allowed signed-root band. -/
theorem carrier_step_dominates {b : ℤ} (hb : 0 < b) (V : ℤ) :
    2 * |V| + 1 < 4 * (1 + b * V ^ 2) := by
  have h := mul_nonneg (show 0 ≤ b - 1 by omega) (sq_nonneg V)
  nlinarith [sq_abs V, sq_nonneg (2 * |V| - 1), abs_nonneg V]

theorem transport_nonneg {b m G V y : ℤ} (hb : 0 < b) (hm : 0 < m)
    (hy : y = 1 + 4 * (b * (m - V ^ 2 * G) - G))
    (hsmall : |y| < 2 * |V|) : 0 ≤ G := by
  by_contra hG
  have hstep := mul_le_mul_of_nonneg_left (show G ≤ -1 by omega)
    (show 0 ≤ 4 * (1 + b * V ^ 2) by positivity)
  have hdom := carrier_step_dominates hb V
  have hbm := mul_pos hb hm
  nlinarith only [hy, hsmall, le_abs_self y, hstep, hdom, hbm]

theorem carrier_exists {b G V y : ℤ} (hb : 0 < b) (hG : 0 < G)
    (hV : 0 < V) (hsmall : -2 * V < y) (hd : b ∣ G)
    (hy : 4 * b ∣ y - 1) :
    ∃ m : ℤ, 0 < m ∧ y = 1 + 4 * (b * (m - V ^ 2 * G) - G) := by
  obtain ⟨g, hg⟩ := hd
  obtain ⟨e, he⟩ := hy
  let m := e + (1 + b * V ^ 2) * g
  have hm : 4 * b * m = y - 1 + 4 * (1 + b * V ^ 2) * G := by
    dsimp [m]
    rw [hg]
    linear_combination -he
  have hdom := carrier_step_dominates hb V
  rw [abs_of_pos hV] at hdom
  have hstep := mul_le_mul_of_nonneg_left (show 1 ≤ G from hG)
    (show 0 ≤ 4 * (1 + b * V ^ 2) by positivity)
  have hm0 : 0 < m := by
    have hprod : 0 < 4 * b * m := by
      nlinarith only [hm, hsmall, hdom, hstep]
    exact pos_of_mul_pos_right hprod (by positivity)
  exact ⟨m, hm0, by nlinarith only [hm]⟩

#print axioms carrier_step_dominates
#print axioms auxiliary_estimates
#print axioms transport_nonneg
#print axioms carrier_exists

end NewAlgebraSimplifications
