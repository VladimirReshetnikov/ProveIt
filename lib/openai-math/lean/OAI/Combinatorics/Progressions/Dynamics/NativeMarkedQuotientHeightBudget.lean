import OAI.Combinatorics.Progressions.Estimates.RealifiedTopQuotient

namespace OAI

section

namespace Erdos3

theorem exists_nativeMarkedQuotientHeightBudget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + A) ^ A ≤ (p + C) ^ C ∧
      quotientInducedMapHeightBudget ((p + A) ^ A) ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let R : Polynomial ℕ := Q + (Q + 3) ^ 7 + 1
  let B : Polynomial ℕ := ((R + 2) ^ 4 + R + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Q + B)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hsum : (p + A) ^ A + quotientInducedMapHeightBudget ((p + A) ^ A) ≤
      (p + C) ^ C := by
    simpa [Q, R, B, quotientInducedMapHeightBudget, Polynomial.eval₂_pow] using hbound p hp
  have hq : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) A
  have hb : 0 ≤ quotientInducedMapHeightBudget ((p + A) ^ A) := by
    unfold quotientInducedMapHeightBudget
    positivity
  exact ⟨(le_add_of_nonneg_right hb).trans hsum,
    (le_add_of_nonneg_left hq).trans hsum⟩

end Erdos3

end

end OAI
