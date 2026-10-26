import Mathlib.Tactic

namespace ProofSimplification.PowerThreshold

theorem sixteen_pow_bound {r : ℕ} (hr : 2 ≤ r) :
    2 ^ (2 * r + 2) + 2 ≤ 16 ^ r := by
  have ht : 16 ≤ 4 ^ r := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 4) hr)
  rw [pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 from rfl]
  rw [show (16 : ℕ) = 4 ^ 2 from rfl, ← pow_mul, Nat.mul_comm 2 r, pow_mul]
  nlinarith

#print axioms sixteen_pow_bound

theorem seventy_two_mul_lt_two_pow {r : ℕ} (hr : 4 ≤ r) :
    72 * r < 2 ^ (2 * r + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h : n < 4 ^ n := Nat.lt_pow_self (by decide : 1 < 4)
  rw [show 2 * (4 + n) + 1 = 9 + 2 * n by omega, pow_add, pow_mul]
  norm_num
  omega

#print axioms seventy_two_mul_lt_two_pow

end ProofSimplification.PowerThreshold
