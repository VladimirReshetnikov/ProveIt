import Mathlib

namespace OAI

section

namespace Erdos3

theorem reference_mean_error_budget {lam τ ε δ η : ℝ}
    (hlam : 0 ≤ lam) (hτ : 0 ≤ τ) (hδ : δ ≤ τ / 8)
    (hε : ε ≤ lam * τ / 8) (hη : η ≤ τ / 8) (hηlam : η ≤ lam * τ / 8) :
    ε + 2 * lam * δ + (1 + lam) * η ≤ lam * τ ∧ δ + η ≤ τ := by
  have hld := mul_le_mul_of_nonneg_left hδ hlam
  have hle := mul_le_mul_of_nonneg_left hη hlam
  have hlt := mul_nonneg hlam hτ
  constructor <;> nlinarith

theorem reference_mean_comparison {H G v lam ε δ η : ℝ}
    (hlam : 0 ≤ lam) (hG : |G - v| ≤ δ + η)
    (hH : H ≤ lam * v + ε + lam * δ + η) :
    H ≤ lam * G + (ε + 2 * lam * δ + (1 + lam) * η) ∧ v - (δ + η) ≤ G := by
  have hlow := (abs_le.mp hG).1
  have hmul := mul_le_mul_of_nonneg_left hlow hlam
  constructor <;> nlinarith

theorem reference_mean_comparison_of_budget {H G v lam τ ε δ η : ℝ}
    (hlam : 0 ≤ lam) (hτ : 0 ≤ τ) (hδ : δ ≤ τ / 8)
    (hε : ε ≤ lam * τ / 8) (hη : η ≤ τ / 8) (hηlam : η ≤ lam * τ / 8)
    (hG : |G - v| ≤ δ + η) (hH : H ≤ lam * v + ε + lam * δ + η) :
    H ≤ lam * G + lam * τ ∧ v - τ ≤ G := by
  obtain ⟨hupper, hlower⟩ := reference_mean_comparison hlam hG hH
  obtain ⟨he, hd⟩ := reference_mean_error_budget hlam hτ hδ hε hη hηlam
  constructor <;> linarith

end Erdos3

end

end OAI
