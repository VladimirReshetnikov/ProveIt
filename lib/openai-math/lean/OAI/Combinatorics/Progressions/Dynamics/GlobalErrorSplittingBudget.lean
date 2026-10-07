import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation

namespace OAI

section

namespace Erdos3

theorem exists_global_error_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ b : ℝ, 0 ≤ b →
      let B := (b + a) ^ a
      let F := (B + c) ^ c
      let Q := 3 * b + B + F + 3
      B ≤ (b + C) ^ C ∧ productNiltestBudget (3 * Q + 4) ≤ (b + C) ^ C := by
  obtain ⟨e, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let B₀ := (X + Polynomial.C a) ^ a
  let F₀ := (B₀ + Polynomial.C c) ^ c
  let Q₀ := 3 * X + B₀ + F₀ + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (3 * Q₀ + 4 + Polynomial.C e) ^ e)
  refine ⟨C, hC, ?_⟩
  intro b hb B F Q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpoly : B + (3 * Q + 4 + e) ^ e ≤ (b + C) ^ C := by
    simpa [X, B₀, F₀, Q₀, B, F, Q, Polynomial.eval₂_pow] using hbudget b hb
  have hnon : 0 ≤ (3 * Q + 4 + e) ^ e := by positivity
  exact ⟨by linarith, (hproduct _ (by positivity)).trans (by linarith)⟩

end Erdos3

end

end OAI
