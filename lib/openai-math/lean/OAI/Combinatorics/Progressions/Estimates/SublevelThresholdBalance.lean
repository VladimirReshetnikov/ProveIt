import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem sublevel_threshold_balance (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧
      (τ / c) ^ (((n * d : ℕ) : ℝ)⁻¹) =
        (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) ∧
      (u / τ) ^ ((d : ℝ)⁻¹) =
        (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let x : ℝ := u / c
  let a : ℝ := (n : ℝ) / (n + 1)
  have hx : 0 < x := div_pos hu hc
  let τ : ℝ := c * x ^ a
  have hτ : 0 < τ := mul_pos hc (Real.rpow_pos_of_pos hx _)
  have hratio : τ / c = x ^ a := by dsimp [τ]; field_simp
  have hexp : a * (((n * d : ℕ) : ℝ)⁻¹) = ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
    dsimp [a]
    push_cast
    field_simp
  have hexp' : (1 - a) * (d : ℝ)⁻¹ = ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
    dsimp [a]
    push_cast
    field_simp
    ring
  have hquot : u / τ = x ^ (1 - a) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    dsimp [τ, x]
    field_simp
  refine ⟨τ, hτ, ?_, ?_⟩
  · rw [hratio, ← Real.rpow_mul hx.le, hexp]
  · rw [hquot, ← Real.rpow_mul hx.le, hexp']

end Erdos3

end

end OAI
