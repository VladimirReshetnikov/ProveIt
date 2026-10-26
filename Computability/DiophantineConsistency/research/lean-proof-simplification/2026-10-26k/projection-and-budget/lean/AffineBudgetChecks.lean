import DiophantineConsistency.AffineBudget

namespace DiophantineConsistency.AffineBudgetChecks
open scoped BigOperators

-- Exact numerical hypotheses supplied by Rep.compose and GraphRep.composeDirect.
theorem direct_case {n C w₀ d₀ W D : ℕ} (w d : Fin n → ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n)
    (hr : d₀ ≤ 6 * w₀ + C) (hs : ∀ i, d i ≤ 6 * w i + C)
    (depth : ∀ h, 1 ≤ h → d₀ ≤ h → (∀ i, d i ≤ h) → D ≤ 2 * n + 2 + h)
    (count : W = n + (w₀ + ∑ i, w i)) : D ≤ 6 * W + C := by
  exact AffineBudget.compose w d hC hr hs depth (by omega : 2 * n + 2 ≤ 6 * n)
    (by rw [count])

-- The ordinary graph composition adds one more output witness.
theorem ordinary_case {n C w₀ d₀ W D : ℕ} (w d : Fin n → ℕ)
    (hC : 1 ≤ C)
    (hr : d₀ ≤ 6 * w₀ + C) (hs : ∀ i, d i ≤ 6 * w i + C)
    (depth : ∀ h, 1 ≤ h → d₀ ≤ h → (∀ i, d i ≤ h) → D ≤ 2 * n + 4 + h)
    (count : W = (n + 1) + (w₀ + ∑ i, w i)) : D ≤ 6 * W + C := by
  exact AffineBudget.compose w d hC hr hs depth (by omega : 2 * n + 4 ≤ 6 * (n + 1))
    (by rw [count])

-- Zero arity is allowed in the ordinary budget, but cannot pay direct overhead.
example : ¬ (2 * 0 + 2 ≤ 6 * 0) := by decide
example : 2 * 0 + 4 ≤ 6 * (0 + 1) := by decide

#print axioms AffineBudget.compose
#print axioms direct_case
#print axioms ordinary_case
end DiophantineConsistency.AffineBudgetChecks
