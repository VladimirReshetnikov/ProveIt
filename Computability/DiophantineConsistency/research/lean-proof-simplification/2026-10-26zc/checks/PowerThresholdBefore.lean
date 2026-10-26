import Mathlib.Tactic

namespace ProofSimplification.PowerThresholdBefore

theorem sixteen_pow_bound {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (2 * r + 2) + 2 ≤ 16 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have h2 : 2 ^ (2 * (r + 1) + 2) = 2 ^ (2 * r + 2) * 4 := by
      rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega,pow_add]
      norm_num
    rw [h2,show 16 ^ (r + 1) = 16 ^ r * 16 by rw [pow_succ]]
    nlinarith [Nat.two_pow_pos (2 * r + 2)]

#print axioms sixteen_pow_bound

theorem seventy_two_mul_lt_two_pow {r : ℕ} (hr : 4 ≤ r) :
    72 * r < 2 ^ (2 * r + 1) := by
  induction r,hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have hstep : 2 ^ (2 * (r + 1) + 1) = 2 ^ (2 * r + 1) * 4 := by
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega,pow_add]
      norm_num
    rw [hstep]
    nlinarith

#print axioms seventy_two_mul_lt_two_pow

end ProofSimplification.PowerThresholdBefore
