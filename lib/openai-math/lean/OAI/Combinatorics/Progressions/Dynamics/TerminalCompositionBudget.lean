import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_terminalComposition_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      p ≤ (p + C) ^ C ∧ (2 * p + a) ^ a ≤ (p + C) ^ C ∧ (2 * p + b) ^ b ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := Polynomial.X +
    (2 * Polynomial.X + Polynomial.C a) ^ a + (2 * Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (2 * p + a) ^ a := by positivity
  have hb : 0 ≤ (2 * p + b) ^ b := by positivity
  have hsum : p + (2 * p + a) ^ a + (2 * p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
