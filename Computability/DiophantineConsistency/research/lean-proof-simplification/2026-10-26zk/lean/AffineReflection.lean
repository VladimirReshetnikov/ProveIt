import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Abs

namespace NewAffineReflection

/-- The affine carrier is positive without any sign assumption on V. -/
theorem affine_carrier_pos {b G V y m : ℤ} (hb : 0 < b) (hG : 0 < G)
    (hsmall : -2 * V < y)
    (hy : y = 1 + 4 * (b * (m - V ^ 2 * G) - G)) : 0 < m := by
  by_contra hm
  have hbm := mul_nonpos_of_nonneg_of_nonpos hb.le (show m ≤ 0 by omega)
  have hAG := mul_nonneg (show 0 ≤ 1 + b * V ^ 2 by positivity)
    (show 0 ≤ G - 1 by omega)
  have hbV := mul_nonneg (show 0 ≤ b - 1 by omega) (sq_nonneg V)
  nlinarith only [hy, hsmall, hbm, hAG, hbV, sq_nonneg (4 * V - 1)]

/-- The existing soundness statement follows by reflecting around y=1. -/
theorem transport_nonneg {b m G V y : ℤ} (hb : 0 < b) (hm : 0 < m)
    (hy : y = 1 + 4 * (b * (m - V ^ 2 * G) - G))
    (hsmall : |y| < 2 * |V|) : 0 ≤ G := by
  by_contra hG
  have hsmall' : -2 * |V| < 2 - y := by have := le_abs_self y; omega
  have hreflect : 2 - y = 1 + 4 * (b * (-m - |V| ^ 2 * -G) - -G) := by
    rw [sq_abs]
    nlinarith only [hy]
  have := affine_carrier_pos hb (show 0 < -G by omega) hsmall' hreflect
  omega

/-- Existing completeness statement, preserving its public assumptions. -/
theorem carrier_exists {b G V y : ℤ} (hb : 0 < b) (hG : 0 < G)
    (hV : 0 < V) (hsmall : -2 * V < y) (hd : b ∣ G)
    (hy : 4 * b ∣ y - 1) :
    ∃ m : ℤ, 0 < m ∧ y = 1 + 4 * (b * (m - V ^ 2 * G) - G) := by
  obtain ⟨g, hg⟩ := hd
  obtain ⟨e, he⟩ := hy
  let m := e + (1 + b * V ^ 2) * g
  have heq : y = 1 + 4 * (b * (m - V ^ 2 * G) - G) := by
    dsimp [m]
    rw [hg]
    linear_combination he
  exact ⟨m, affine_carrier_pos hb hG hsmall heq, heq⟩

#print axioms affine_carrier_pos
#print axioms transport_nonneg
#print axioms carrier_exists
end NewAffineReflection
