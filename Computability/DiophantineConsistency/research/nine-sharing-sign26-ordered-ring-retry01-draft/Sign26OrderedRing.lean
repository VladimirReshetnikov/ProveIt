import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! SOURCE-ONLY: congruence and conditional ordered-ring gap sign. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Sign26OrderedRing
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem congruence (a n t Q : R) :
    (a * (a + 1) + t - a * n) * ((a + 1) * (a + 1)) -
      ((a - n) * Q + (n + t) * ((a + 1) * (a + 1))) =
      -(a - n) * (Q - ((a + 1) * (a + 1) * (a + 1))) := by
  ring

theorem gap_nonneg (a H n t z : R)
    (ha : 1 ≤ a) (hH : 1 ≤ H) (hn : 1 ≤ n) (ht : 1 ≤ t) (hz : 0 ≤ z)
    (hNt : H * (a + 1 - n - t) = n + z * a) :
    0 ≤ a * (a + 1) + t - a * n := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hr : 0 < H * (a + 1 - n - t) := by
    rw [hNt]
    exact add_pos_of_pos_of_nonneg hnpos (mul_nonneg hz ha0)
  have hd : 0 < a + 1 - n - t := (mul_pos_iff_of_pos_left hHpos).mp hr
  have hq : 0 ≤ a + 1 - n := by linarith
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hg : 0 ≤ a * (a + 1 - n) + t := add_nonneg (mul_nonneg ha0 hq) ht0
  convert hg using 1 <;> ring
end Sign26OrderedRing
#print axioms Sign26OrderedRing.congruence
#print axioms Sign26OrderedRing.gap_nonneg
