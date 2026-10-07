import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedCanonicalGeometry_budget (A C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {P : ℝ}, 0 ≤ P →
      let Q := P + (2 * P + A) ^ A + 2
      0 ≤ Q ∧ P ≤ Q ∧ (P + P + A) ^ A ≤ Q ∧
        (Q + C) ^ C ≤ (P + D) ^ D := by
  let X : Polynomial ℕ := Polynomial.X
  let q := X + (2 * X + Polynomial.C A) ^ A + 2
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget ((q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro P hP Q
  have hpow : 0 ≤ (2 * P + A) ^ A := by positivity
  refine ⟨by dsimp only [Q]; positivity, ?_, ?_, ?_⟩
  · dsimp only [Q]
    linarith only [hpow]
  · have heq : P + P + A = 2 * P + A := by ring
    rw [heq]
    dsimp only [Q]
    linarith only [hP]
  · simpa [q, X, Q, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
