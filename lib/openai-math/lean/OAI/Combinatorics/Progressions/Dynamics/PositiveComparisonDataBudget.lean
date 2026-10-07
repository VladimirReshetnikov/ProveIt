import OAI.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def positiveComparisonDataBudget (m q : ℕ) (p : ℝ) : ℝ :=
  (2 * p + 4) + allocatedFourierOutputBudget m (2 * p + 4) +
    allocatedFourierLogBudget m (2 * p + 4) + 3 * p + (q + 1) * (4 * p + 5) + 4

theorem positiveComparisonDataBudget_bounds (m q : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let Q := positiveComparisonDataBudget m q p
    0 ≤ Q ∧ p ≤ Q ∧ 2 * p + 4 ≤ Q ∧
      allocatedFourierOutputBudget m (2 * p + 4) ≤ Q ∧
      allocatedFourierLogBudget m (2 * p + 4) + 3 * p + (q + 1) * (4 * p + 5) + 4 ≤ Q := by
  have hB := allocatedFourierLogBudget_nonneg m (by linarith : 0 ≤ 2 * p + 4)
  have hF : 0 ≤ allocatedFourierOutputBudget m (2 * p + 4) := by
    unfold allocatedFourierOutputBudget
    positivity
  have hL : 0 ≤ ((q : ℝ) + 1) * (4 * p + 5) := by positivity
  dsimp only [positiveComparisonDataBudget]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem exists_positiveComparisonDataBudget_bound (m q : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → positiveComparisonDataBudget m q p ≤ (p + a) ^ a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierOutputBudget_bound m
  obtain ⟨a, ha, haBound⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 4) + 2 * (2 * Polynomial.X + 4 + Polynomial.C b) ^ b +
      3 * Polynomial.X + Polynomial.C (q + 1) * (4 * Polynomial.X + 5) + 4)
  refine ⟨a, ha, ?_⟩
  intro p hp
  have hP : 0 ≤ 2 * p + 4 := by linarith
  have hB := allocatedFourierLogBudget_nonneg m hP
  have hBF : allocatedFourierLogBudget m (2 * p + 4) ≤ allocatedFourierOutputBudget m (2 * p + 4) := by
    have h := (allocatedFourierOutputBudget_dominates m hP).2.2
    have hnonneg : 0 ≤ 2 * allocatedFourierLogBudget m (2 * p + 4) *
        (2 * allocatedFourierLogBudget m (2 * p + 4) + 2) ^ 4 := by positivity
    linarith
  have hpoly : (2 * p + 4) + 2 * (2 * p + 4 + b) ^ b + 3 * p +
      (q + 1 : ℕ) * (4 * p + 5) + 4 ≤ (p + a) ^ a := by
    simpa [Polynomial.eval₂_pow] using haBound p hp
  apply le_trans _ hpoly
  unfold positiveComparisonDataBudget
  have hF := hb (2 * p + 4) hP
  push_cast
  linarith

end Erdos3.VectorPolynomial

end

end OAI
