import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem rat_nat_div_integer_of_dvd {m n : ℕ} (h : n ∣ m) :
    ∃ z : ℤ, (m : ℚ) / n = (z : ℚ) := by
  obtain ⟨d, rfl⟩ := h
  by_cases hn : n = 0
  · exact ⟨0, by simp [hn]⟩
  · exact ⟨d, by push_cast; field_simp⟩

theorem factorial_log_scalar_integer (s k : ℕ) (hk : k ≤ s) :
    ∃ z : ℤ, (s.factorial : ℚ) * ((-1 : ℚ) ^ (k + 1) / k) = (z : ℚ) := by
  by_cases hzero : k = 0
  · exact ⟨0, by simp [hzero]⟩
  obtain ⟨z, hz⟩ := rat_nat_div_integer_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero hzero) hk)
  refine ⟨(-1 : ℤ) ^ (k + 1) * z, ?_⟩
  push_cast
  rw [show (s.factorial : ℚ) * ((-1 : ℚ) ^ (k + 1) / k) =
    (-1 : ℚ) ^ (k + 1) * ((s.factorial : ℚ) / k) by ring, hz]

theorem factorial_exp_scalar_integer (s k : ℕ) (hk : k ≤ s) :
    ∃ z : ℤ, (k.factorial : ℚ)⁻¹ * (s.factorial : ℚ) ^ k = (z : ℚ) := by
  cases k with
  | zero => exact ⟨1, by simp⟩
  | succ k =>
    have hd : (k + 1).factorial ∣ s.factorial ^ (k + 1) := by
      rw [pow_succ']
      exact (Nat.factorial_dvd_factorial hk).trans (Nat.dvd_mul_right _ _)
    obtain ⟨z, hz⟩ := rat_nat_div_integer_of_dvd hd
    exact ⟨z, by simpa only [Nat.cast_pow, div_eq_mul_inv, mul_comm] using hz⟩

end Erdos3

end

end OAI
