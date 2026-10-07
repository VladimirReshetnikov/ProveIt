import OAI.Combinatorics.Progressions.Geometry.BoxBlockBudget

namespace OAI

section

namespace Erdos3

theorem residueBlock_long_side_budget {θ : ℝ} {N q Q H : ℕ}
    (hθ : 0 < θ) (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (hH : (N : ℝ) / (2 * q * Q) ≤ H) (n : ℕ) :
    θ * N / (4 * q * Q * (n + 1 : ℝ)) ≤ θ * H / (2 * (n + 1 : ℝ)) ∧
      0 < θ * H / (2 * (n + 1 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHr : (0 : ℝ) < H := (by positivity : 0 < (N : ℝ) / (2 * q * Q)).trans_le hH
  refine ⟨?_, by positivity⟩
  calc
    _ = (θ / (2 * (n + 1 : ℝ))) * ((N : ℝ) / (2 * q * Q)) := by
      field_simp
      ring
    _ ≤ (θ / (2 * (n + 1 : ℝ))) * H :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by ring

theorem residueBlock_long_side_budget_of_inverse_mesh {θ : ℝ} {N q Q H : ℕ}
    (hθ : 0 < θ) (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (hH : (1 / (Q : ℝ)) * N / (2 * q) ≤ H) (n : ℕ) :
    θ * N / (4 * q * Q * (n + 1 : ℝ)) ≤ θ * H / (2 * (n + 1 : ℝ)) ∧
      0 < θ * H / (2 * (n + 1 : ℝ)) := by
  apply residueBlock_long_side_budget hθ hN hq hQ _ n
  convert hH using 1
  ring

end Erdos3

end

end OAI
