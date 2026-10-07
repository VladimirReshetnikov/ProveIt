import Mathlib

namespace OAI

section

namespace Erdos3

theorem exists_schmidt_shorter_interval {K : ℝ} (hK : 0 < K) (N : ℕ)
    (hN : 2 * K ≤ N) :
    ∃ H : ℕ, 0 < H ∧ K * H ≤ N ∧ (N : ℝ) ≤ 2 * K * H := by
  let H := ⌊(N : ℝ) / K⌋₊
  have hquot : 2 ≤ (N : ℝ) / K := (le_div_iff₀ hK).mpr (by nlinarith)
  have hH : 1 ≤ H := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; linarith)
  have hupper : K * (H : ℝ) ≤ N := by
    have h := Nat.floor_le (show 0 ≤ (N : ℝ) / K by positivity)
    simpa only [mul_comm] using (le_div_iff₀ hK).mp h
  have hlower : (N : ℝ) < K * ((H : ℝ) + 1) := by
    exact (div_lt_iff₀ hK).mp (Nat.lt_floor_add_one ((N : ℝ) / K)) |>.trans_eq (by ring)
  refine ⟨H, by omega, hupper, ?_⟩
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  nlinarith

theorem schmidt_monomial_interval_budget (j : ℕ) {H N Q B S ε : ℝ}
    (hH : 0 ≤ H) (hN : 0 < N) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hHQ : H * Q ≤ N) (hHBS : H * B * S ≤ ε * N) :
    H ^ (j + 1) * Q ^ j * (B / N ^ (j + 1)) * S ≤ ε := by
  have hp := pow_le_pow_left₀ (mul_nonneg hH hQ) hHQ j
  have hmul := mul_le_mul hp hHBS (by positivity : 0 ≤ H * B * S)
    (pow_nonneg hN.le j)
  have hid : H ^ (j + 1) * Q ^ j * (B / N ^ (j + 1)) * S =
      ((H * Q) ^ j * (H * B * S)) / N ^ (j + 1) := by
    rw [mul_pow, pow_succ H]
    ring
  rw [hid]
  apply (div_le_iff₀ (pow_pos hN _)).mpr
  calc
    _ ≤ N ^ j * (ε * N) := hmul
    _ = ε * N ^ (j + 1) := by rw [pow_succ]; ring

end Erdos3

end

end OAI
