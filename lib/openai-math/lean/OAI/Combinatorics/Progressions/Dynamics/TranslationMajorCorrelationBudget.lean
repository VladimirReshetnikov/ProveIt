import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

def translationMajorPairBudget (a : ℕ) (p : ℝ) : ℝ :=
  (raisedNiltestBudget p + (a : ℝ)) ^ a

theorem translationMajorPairBudget_controls (a : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : 2 ≤ a) :
    p ≤ raisedNiltestBudget p ∧
      raisedNiltestBudget p ≤ translationMajorPairBudget a p ∧
      2 ≤ translationMajorPairBudget a p := by
  have hq : (2 : ℝ) ≤ raisedNiltestBudget p := by
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  have hbase : (1 : ℝ) ≤ raisedNiltestBudget p + a := by
    linarith [Nat.cast_nonneg a (α := ℝ)]
  have hpow : raisedNiltestBudget p + a ≤ translationMajorPairBudget a p := by
    exact (pow_one (raisedNiltestBudget p + a)).symm.le.trans
      (pow_le_pow_right₀ hbase (by omega : 1 ≤ a))
  have hqr : raisedNiltestBudget p ≤ translationMajorPairBudget a p :=
    (le_add_of_nonneg_right (Nat.cast_nonneg a)).trans hpow
  exact ⟨le_raisedNiltestBudget p, hqr, hq.trans hqr⟩

theorem exists_translationMajorCorrelationBudget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      translationMajorPairBudget a p ≤ (p + C) ^ C ∧
        (translationMajorPairBudget a p + (b : ℝ)) ^ b ≤ (p + C) ^ C := by
  let R : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + 2) ^ 2 + 3 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have htotal : translationMajorPairBudget a p +
      (translationMajorPairBudget a p + (b : ℝ)) ^ b ≤ (p + C) ^ C := by
    simpa [R, translationMajorPairBudget, raisedNiltestBudget, Polynomial.eval₂_pow]
      using hbound p hp
  have hr : 0 ≤ translationMajorPairBudget a p := by
    unfold translationMajorPairBudget raisedNiltestBudget
    positivity
  have hproduct : 0 ≤ (translationMajorPairBudget a p + (b : ℝ)) ^ b := by positivity
  exact ⟨(le_add_of_nonneg_right hproduct).trans htotal,
    (le_add_of_nonneg_left hr).trans htotal⟩

end Erdos3

end

end OAI
