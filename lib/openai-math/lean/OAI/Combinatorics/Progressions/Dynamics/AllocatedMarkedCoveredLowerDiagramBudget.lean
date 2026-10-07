import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_allocatedMarkedCoveredLowerDiagramBudget (A B T : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 1 ≤ p →
      let nativeCost := (p + A) ^ A
      let inputCost := p + nativeCost
      let recoveryCost := (inputCost + B) ^ B
      let lowerInput := inputCost + recoveryCost
      let finalLower := (lowerInput + T) ^ T
      1 ≤ inputCost ∧ p ≤ inputCost ∧ nativeCost ≤ inputCost ∧
        inputCost ≤ lowerInput ∧ recoveryCost ≤ lowerInput ∧
        lowerInput ≤ (p + C) ^ C ∧ finalLower ≤ (p + C) ^ C := by
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let I : Polynomial ℕ := Polynomial.X + N
  let R : Polynomial ℕ := (I + Polynomial.C B) ^ B
  let U : Polynomial ℕ := I + R
  let F : Polynomial ℕ := (U + Polynomial.C T) ^ T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + F)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let nativeCost := (p + A) ^ A
  let inputCost := p + nativeCost
  let recoveryCost := (inputCost + B) ^ B
  let lowerInput := inputCost + recoveryCost
  let finalLower := (lowerInput + T) ^ T
  have hnative : 0 ≤ nativeCost := by dsimp [nativeCost]; positivity
  have hinput : 0 ≤ inputCost := add_nonneg hp0 hnative
  have hrecovery : 0 ≤ recoveryCost := by dsimp [recoveryCost]; positivity
  have hlower : 0 ≤ lowerInput := add_nonneg hinput hrecovery
  have hfinal : 0 ≤ finalLower := by dsimp [finalLower]; positivity
  have hsum : lowerInput + finalLower ≤ (p + C) ^ C := by
    simpa only [N, I, R, U, F, nativeCost, inputCost, recoveryCost, lowerInput, finalLower,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Nat.coe_castRingHom] using hbudget p hp0
  exact ⟨hp.trans (le_add_of_nonneg_right hnative), le_add_of_nonneg_right hnative,
    le_add_of_nonneg_left hp0, le_add_of_nonneg_right hrecovery,
    le_add_of_nonneg_left hinput, (le_add_of_nonneg_right hfinal).trans hsum,
    (le_add_of_nonneg_left hlower).trans hsum⟩

end Erdos3

end

end OAI
