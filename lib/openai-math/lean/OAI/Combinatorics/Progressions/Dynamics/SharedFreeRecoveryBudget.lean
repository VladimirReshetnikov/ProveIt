import OAI.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold

namespace OAI

section

namespace Erdos3

theorem exists_sharedFreeRecoveryThreshold_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeRecoveryThreshold s q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := (4 * X + (X + V (4 * X)) + 3) ^ 7
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let I : Polynomial ℕ := Polynomial.X + H B +
    ((B + 3) ^ 2 + Polynomial.C s * Polynomial.X) + ((Polynomial.X + 2) ^ 3 + Polynomial.X)
  let Z : Polynomial ℕ := 8 * I + 1
  let A : Polynomial ℕ := 4 * Polynomial.X + (F (Polynomial.X + H Polynomial.X) + 1) +
    (Z + ((Z + 2) ^ 3 + (Z + 2) ^ 36))
  let T : Polynomial ℕ := (Z + 2) ^ 48 + (Z + 2) ^ 24 + Z + 1 + (A + 2) ^ 5
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hH : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hF : fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) ≤
      fourRefinementAnnihilatorBudget (p + coefficientFourHeightBudget p) := by
    unfold fourRefinementAnnihilatorBudget fourRefinementBasisBudget preimageBasisBudget
      sparseGeneratorBudget
    gcongr
  have hA : sharedFreeEquationInputBudget s q p ≤ sharedFreeEquationInputBudget s p p := by
    unfold sharedFreeEquationInputBudget
    linarith
  have hA0 := (sharedFreeEquationInputBudget_bounds s hq hp).1
  have hAp0 := (sharedFreeEquationInputBudget_bounds s hp hp).1
  have hz : 0 ≤ 8 * sharedRefinementInputBudget s p + 1 := by
    have h := (sharedRefinementInputBudget_bounds s hp).2.2.1
    linarith
  have hsep := separationBudget_nonneg hz
  have hupper : sharedFreeRecoveryThreshold s q p ≤
      separationBudget (8 * sharedRefinementInputBudget s p + 1) +
        (sharedFreeEquationInputBudget s p p + 2) ^ 5 := by
    unfold sharedFreeRecoveryThreshold
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · apply le_trans (pow_le_pow_left₀ (by positivity) (by linarith :
        sharedFreeEquationInputBudget s q p + 2 ≤ sharedFreeEquationInputBudget s p p + 2) 5)
      exact le_add_of_nonneg_left hsep
  apply hupper.trans
  simpa [T, A, Z, I, B, F, V, G, H, R, sharedFreeEquationInputBudget,
    sharedRefinementInputBudget, coefficientFourHeightBudget, refiltrationCoordinateBudget,
    fourRefinementAnnihilatorBudget, fourRefinementBasisBudget, preimageBasisBudget,
    sparseGeneratorBudget, separationBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
