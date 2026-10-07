import OAI.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget
import OAI.Combinatorics.Progressions.Linear.RecoveredKernelScalarBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedFinalScalarBudget (m degree : ℕ) (t : ℝ) : ℝ :=
  2048 * t ^ 3 + (t + 2) ^ (preparedIntegralBasisExponent m + 1) +
    2 * t + 1 + degree * t

theorem exists_preparedFinalScalar_power_budget (m degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      spatialPatchExtractionCost
          (recoveredKernelScalarBudget (preparedFinalScalarBudget m degree t)) ≤
        (t + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B : Polynomial ℕ := 2048 * X ^ 3 +
    (X + 2) ^ (preparedIntegralBasisExponent m + 1) +
      2 * X + 1 + Polynomial.C degree * X
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (20 * (8 * (B + 1) ^ 2 + 1) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro t ht
  simpa [B, X, preparedFinalScalarBudget, recoveredKernelScalarBudget,
    spatialPatchExtractionCost, Polynomial.eval₂_pow] using hbound t (by linarith)

end Erdos3.VectorPolynomial

end

end OAI
