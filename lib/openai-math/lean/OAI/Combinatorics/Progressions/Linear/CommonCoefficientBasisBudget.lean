import OAI.Combinatorics.Progressions.Estimates.CommonFreeSunflower

namespace OAI

section

namespace Erdos3

theorem coefficientSpaceBasisBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → coefficientSpaceBasisBudget p ≤ (p + C) ^ C := by
  let S (x : Polynomial ℕ) := x + x * ((x + 2) ^ 7 + x)
  let B (x : Polynomial ℕ) := S (x + (x + (x + 3) ^ 7 + 2) ^ 4 + 1)
  let D (x : Polynomial ℕ) := B (x + S (4 * x + 1))
  let R : Polynomial ℕ := ((Polynomial.X + 1 + (Polynomial.X + 3) ^ 7 + 2) ^ 9 +
    Polynomial.X + 4) ^ 4
  let H : Polynomial ℕ := Polynomial.X + Polynomial.X * (R + 1 + (Polynomial.X + 3) ^ 7)
  let A : Polynomial ℕ := Polynomial.X + 4 * Polynomial.X + H + (Polynomial.X + 3) ^ 7 + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (B (A + (A + 2) ^ 4 + D A))
  refine ⟨C, hC, fun p hp => ?_⟩
  have h := hbound p hp
  simpa [S, B, D, R, H, A, coefficientSpaceBasisBudget, coefficientSpaceInputBudget,
    dependentCoordinateBudget, preimageBasisBudget, sparseGeneratorBudget,
    horizontalCoordinateBudget, refiltrationCoordinateBudget, Polynomial.eval₂_pow] using h

end Erdos3

end

end OAI
