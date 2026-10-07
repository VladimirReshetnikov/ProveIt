import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_native_dependent_selection_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P₀ := (p + a) ^ a
      let P := (P₀ + 2) ^ 3 + 2 * P₀
      P₀ ≤ (p + C) ^ C ∧ 2 * P ≤ (p + C) ^ C ∧ (P + c) ^ c ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + Polynomial.C a) ^ a
  let P := (P₀ + 2) ^ 3 + 2 * P₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P₀ + 2 * P + (P + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp P₀' P'
  have hP₀ : 0 ≤ P₀' := by dsimp only [P₀']; positivity
  have hP : 0 ≤ P' := by dsimp only [P']; positivity
  have hpow : 0 ≤ (P' + c) ^ c := by positivity
  have hsum : P₀' + 2 * P' + (P' + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, P₀, P, P₀', P', Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hP, hpow, hsum],
    by linarith only [hP₀, hpow, hsum], by linarith only [hP₀, hP, hsum]⟩

end Erdos3

end

end OAI
