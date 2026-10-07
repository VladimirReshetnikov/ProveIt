import OAI.Combinatorics.Progressions.Probability.LowDensityAmplification

namespace OAI

section

namespace Erdos3

theorem exists_relative_amplification_discount (s : ℕ) {H : ℝ} (hH : 1 < H) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧
      let κ := (1 - τ) ^ (s + 1)
      0 < κ ∧ κ < 1 ∧ 1 < κ * H ∧ 1 ≤ κ ^ 2 * H := by
  have hH0 : 0 < H := by linarith
  have hn : (1 : ℝ) ≤ (s + 1 : ℕ) := by exact_mod_cast Nat.succ_pos s
  let τ := (H - 1) / (4 * (s + 1 : ℕ) * H)
  have ht : 0 < τ := div_pos (by linarith) (by positivity)
  have ht4 : τ ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (s + 1 : ℕ) * H)).mpr
    have hm := mul_le_mul_of_nonneg_right hn hH0.le
    nlinarith
  have ht1 : 0 < 1 - τ := by linarith
  let κ := (1 - τ) ^ (s + 1)
  have hk : 0 < κ := pow_pos ht1 _
  have hk1 : κ < 1 := pow_lt_one₀ ht1.le (by linarith) (by omega)
  have hbern := one_add_mul_le_pow (a := -τ) (by linarith : -2 ≤ -τ) (2 * (s + 1))
  have hpow : (1 + -τ) ^ (2 * (s + 1)) = κ ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
    rfl
  rw [hpow] at hbern
  have heq : 4 * (s + 1 : ℕ) * H * τ = H - 1 := by
    dsimp only [τ]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hbern hH0.le
  push_cast at hmul heq
  have hsq : 1 ≤ κ ^ 2 * H := by nlinarith
  have hkk : κ ^ 2 < κ := by nlinarith
  have hgain : 1 < κ * H := hsq.trans_lt (mul_lt_mul_of_pos_right hkk hH0)
  exact ⟨τ, ht, by linarith, hk, hk1, hgain, hsq⟩

end Erdos3

end

end OAI
