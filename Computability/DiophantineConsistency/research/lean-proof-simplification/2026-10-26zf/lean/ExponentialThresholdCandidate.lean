import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Uncompiled candidate. Same natural-number statement as the maintained
NativePellPower theorem, with no induction on the exponent. -/
namespace ProofDelta.ExponentialThreshold

theorem sixteen_pow_bound {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (2 * r + 2) + 2 ≤ 16 ^ r := by
  have ht : 16 ≤ 4 ^ r := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 4) hr
  calc
    2 ^ (2 * r + 2) + 2 = 4 * 4 ^ r + 2 := by
      rw [pow_add, pow_mul]; ring
    _ ≤ (4 ^ r) ^ 2 := by
      nlinarith [Nat.mul_le_mul_left (4 ^ r) ht]
    _ = 16 ^ r := by
      rw [← pow_mul, mul_comm r 2, pow_mul]; norm_num

#print axioms sixteen_pow_bound
end ProofDelta.ExponentialThreshold
