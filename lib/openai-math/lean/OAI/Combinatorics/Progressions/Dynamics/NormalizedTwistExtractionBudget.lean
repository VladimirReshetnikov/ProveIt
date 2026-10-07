import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_normalizedTwistExtractionBudget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a + 3 * p + 16
      q + (q + b) ^ b + 3 * p + 16 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a + 3 * X + 16
  let P := Q + (Q + Polynomial.C b) ^ b + 3 * X + 16
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, X, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
