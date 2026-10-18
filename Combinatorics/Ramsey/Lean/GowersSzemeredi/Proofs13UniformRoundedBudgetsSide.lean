import GowersSzemeredi.Proofs13UniformRoundedBudgets

/-! Declarations of `Proofs13UniformRoundedBudgets` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Filter

/-- A factor-two exponent margin permits a threshold depending only on lower
bounds for the target coefficient, target exponent, and Bohr radius. -/
theorem uniform_rounded_power_budgets
    {c₀ d z₀ e₀ : Real} (hc₀ : 0 < c₀) (hd : 0 < d) (hdone : d ≤ 1)
    (hz₀ : 0 < z₀) (he₀ : 0 < e₀) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ c e u v w z P Q : Real,
      c₀ ≤ c → c ≤ 1 / 2 → e₀ ≤ e → 2 * e ≤ 1 →
      0 < v → v ≤ 1 → 0 < w → w ≤ 1 → z₀ ≤ z →
      2 * e ≤ u * v → 2 * e ≤ u * w →
      d * (N : Real) ^ u ≤ P → P ^ v / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
        c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m := by
  refine ⟨Nat.ceil (uniformRoundedPowerThreshold c₀ d z₀ e₀), ?_⟩
  intro N hN
  exact uniform_rounded_power_budgets_explicit hc₀ hd hdone hz₀ he₀ N
    ((Nat.le_ceil _).trans (by exact_mod_cast hN))

end

end LeanProofs.GowersSzemeredi
