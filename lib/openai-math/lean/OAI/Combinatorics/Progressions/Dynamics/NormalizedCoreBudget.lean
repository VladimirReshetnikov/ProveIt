import OAI.Combinatorics.Progressions.Geometry.GeometricSpectralBudgets

namespace OAI

section

namespace Erdos3

theorem retained_core_allowance_spec {ε : ℝ} (hε : 0 < ε) :
    0 < ε / (2 + ε) ∧ ε / (2 + ε) ≤ 1 ∧ (ε / (2 + ε)) * (2 + ε) ≤ ε := by
  have hd : 0 < 2 + ε := by linarith
  refine ⟨div_pos hε hd, (div_le_one hd).mpr (by linarith), ?_⟩
  exact le_of_eq (div_mul_cancel₀ ε hd.ne')

theorem normalized_core_error_budget {ξ P κ A B M N : ℝ} {r : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hMN : M * N ≤ Real.exp P)
    (hr : CyclicCrootSisask.spectralIterations ξ P ≤ r)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) :
    κ * A ^ 2 * B ^ 2 ≤ 1 / 2 ∧
      4 * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N) ≤ ξ := by
  have ht := geometric_tail_after_cutoff hξ hκ0 hκhalf (mul_nonneg hM hN) hMN hr
  rw [← mul_assoc] at ht
  constructor <;> nlinarith

theorem normalized_core_error_of_power_cutoff {ξ P Q t κ A B L M N : ℝ} {d e r : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ht : 2 ≤ t) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hMN : M * N ≤ Real.exp P)
    (hr : CyclicCrootSisask.spectralIterations ξ P ≤ r)
    (hL0 : 0 ≤ L) (hL : L ≤ Real.exp Q) (hAB : A ^ 2 * B ^ 2 ≤ L * t ^ d)
    (hκ : κ ≤ (t ^ (d + e))⁻¹) (he : CyclicCrootSisask.spectralIterations ξ Q ≤ e) :
    κ * A ^ 2 * B ^ 2 ≤ 1 / 2 ∧
      4 * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N) ≤ ξ := by
  exact normalized_core_error_budget hξ hξ1 hκ0 hκhalf hM hN hMN hr
    (low_level_after_power_cutoff hξ ht hL0 hL hAB hκ he)

end Erdos3

end

end OAI
