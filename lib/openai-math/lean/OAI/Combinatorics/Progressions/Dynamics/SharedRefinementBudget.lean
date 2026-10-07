import OAI.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators

namespace OAI

section

namespace Erdos3

def sharedRefinementInputBudget (s : ℕ) (p : ℝ) : ℝ :=
  let B := (p + 2) ^ 3 + 2 * p
  p + coefficientFourHeightBudget B + ((B + 3) ^ 2 + (s : ℝ) * p) + ((p + 2) ^ 3 + p)

theorem sharedRefinementInputBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let B := (p + 2) ^ 3 + 2 * p
    let A := sharedRefinementInputBudget s p
    0 ≤ B ∧ p ≤ B ∧ 0 ≤ A ∧ p ≤ A ∧ coefficientFourHeightBudget B ≤ A ∧
      (B + 3) ^ 2 + (s : ℝ) * p ≤ A ∧ (p + 2) ^ 3 + p ≤ A := by
  intro B A
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpB : p ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (p + 2)]
  have hH := coefficientFourHeightBudget_nonneg hB
  have hE : 0 ≤ (B + 3) ^ 2 + (s : ℝ) * p := by positivity
  have hL : 0 ≤ (p + 2) ^ 3 + p := by positivity
  have hA : A = p + coefficientFourHeightBudget B + ((B + 3) ^ 2 + (s : ℝ) * p) +
      ((p + 2) ^ 3 + p) := rfl
  refine ⟨hB, hpB, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Erdos3

end

end OAI
