import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_fastSymbolCorrectionBudget (a ce cr : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p →
      let p₀ : ℝ := p + (p + 2) ^ a + (p + 2) ^ 4 + 2
      let p₁ : ℝ := p₀ + (p₀ + ce) ^ ce + (p₀ + cr) ^ cr
      let p₂ : ℝ := p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 + 2
      (p₂ + ce) ^ ce + (p₂ + cr) ^ cr ≤ (p + C) ^ C := by
  let B₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ 4 + 2
  let B₁ : Polynomial ℕ := B₀ + (B₀ + Polynomial.C ce) ^ ce + (B₀ + Polynomial.C cr) ^ cr
  let B₂ : Polynomial ℕ := B₁ + ((B₁ + 2) ^ 10 + 2) ^ 36 + ((B₁ + 2) ^ 10 + 2) ^ 18 + 2
  let B : Polynomial ℕ := (B₂ + Polynomial.C ce) ^ ce + (B₂ + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, B₂, B₁, B₀, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
