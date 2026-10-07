import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def centralActionBudget (p : ℝ) : ℝ := (p + 3) ^ 9 + 2 * p + 2

def verticalDecompositionBudget (p : ℝ) : ℝ :=
  let q := centralActionBudget p
  2 * q * (2 * q + 2) ^ 4 + ((2 * q + 2) ^ 4 + q + (p + 3) ^ 5 + 2) ^ 4

theorem centralActionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ centralActionBudget p := by
  unfold centralActionBudget
  positivity

theorem le_centralActionBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ centralActionBudget p := by
  have h : 0 ≤ (p + 3) ^ 9 := by positivity
  unfold centralActionBudget
  linarith

theorem verticalDecompositionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ verticalDecompositionBudget p := by
  unfold verticalDecompositionBudget
  have := centralActionBudget_nonneg hp
  positivity

theorem exists_verticalDecompositionBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → verticalDecompositionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + 3) ^ 9 + 2 * Polynomial.X + 2
  let P : Polynomial ℕ :=
    2 * Q * (2 * Q + 2) ^ 4 + ((2 * Q + 2) ^ 4 + Q + (Polynomial.X + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, verticalDecompositionBudget, centralActionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
