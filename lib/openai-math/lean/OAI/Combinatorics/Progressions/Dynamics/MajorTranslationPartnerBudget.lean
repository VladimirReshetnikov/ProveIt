import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

theorem exists_majorTranslationPartnerBudget_bound (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      productNiltestBudget ((p + a) ^ a + raisedNiltestBudget p + 2) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a + (X + (X + 2) ^ 2 + 3) + 2
  let P := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, X, Polynomial.eval₂_pow, productNiltestBudget,
    productObservableLipBudget, raisedNiltestBudget] using hbound p hp

end Erdos3

end

end OAI
