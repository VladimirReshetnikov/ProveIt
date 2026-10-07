import OAI.Combinatorics.Progressions.Estimates.SharedFreeComparisonDescent

namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeLowerComparisonBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (sharedFreeComparisonModelBudget s q p + rankUnitDescentConstant s) ^ rankUnitDescentConstant s

theorem exists_sharedFreeLowerComparisonBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeLowerComparisonBudget s q p ≤ (p + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_sharedFreeComparisonModelBudget_bound s
  let a := rankUnitDescentConstant s
  let P : Polynomial ℕ := ((Polynomial.X + Polynomial.C b) ^ b + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hM : 0 ≤ sharedFreeComparisonModelBudget s q p := by
    have hH := sharedFreeComparisonBasisBudget_nonneg hq hp
    unfold sharedFreeComparisonModelBudget
    positivity
  have hsmall : sharedFreeComparisonModelBudget s q p + a ≤ (p + b) ^ b + a := by
    linarith [hb q p hq hqp hp]
  apply (pow_le_pow_left₀ (add_nonneg hM (Nat.cast_nonneg a)) hsmall a).trans
  simpa [P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
