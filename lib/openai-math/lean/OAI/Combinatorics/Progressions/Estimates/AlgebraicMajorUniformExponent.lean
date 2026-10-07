import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_algebraicMajor_uniform_exponent (d a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let B := (p + a) ^ a
      (((d + 1) ^ 2 + 3 : ℕ) : ℝ) * (B + 2) ≤ (p + C) ^ C ∧
        2 * (((d + 1) ^ 2 + 1 : ℕ) : ℝ) * B ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let P := Polynomial.C ((d + 1) ^ 2 + 3) * (Q + 2) +
    2 * Polynomial.C ((d + 1) ^ 2 + 1) * Q
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  dsimp only
  have htotal :
      (((d + 1) ^ 2 + 3 : ℕ) : ℝ) * ((p + a) ^ a + 2) +
        2 * (((d + 1) ^ 2 + 1 : ℕ) : ℝ) * (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Q, X, Polynomial.eval₂_pow] using hbound p hp
  constructor
  · exact (le_add_of_nonneg_right (by positivity)).trans htotal
  · exact (le_add_of_nonneg_left (by positivity)).trans htotal

end Erdos3

end

end OAI
