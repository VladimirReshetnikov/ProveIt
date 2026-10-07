import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

theorem exists_masked_comparison_budget (a b : ℕ) {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 2 ≤ p →
      let R := (p + 2) ^ (max a b)
      (p + 2) ^ a ≤ R ∧ (p + 2) ^ b ≤ R ∧
      R + 1 ≤ (p + 2) ^ C ∧
      productNiltestBudget (raisedNiltestBudget R) ≤ (p + 2) ^ C ∧
      Real.exp (-((p + 2) ^ C)) ≤ xi := by
  obtain ⟨ell, hell⟩ := exists_nat_ge (-Real.log xi)
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + 2) ^ (max a b)
  let Q := Y + (Y + 2) ^ 2 + 3
  let E := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (E + Y + 1 + Polynomial.C ell)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  have hp0 : 0 ≤ p := by linarith
  have hell0 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hbase : 1 ≤ p + 2 := by linarith
  have hR0 : 0 ≤ (p + 2) ^ (max a b) := pow_nonneg (by linarith) _
  have hQ0 : 0 ≤ raisedNiltestBudget ((p + 2) ^ (max a b)) :=
    hR0.trans (le_raisedNiltestBudget _)
  have hE0 : 0 ≤ productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) :=
    (sq_nonneg _).trans (productNiltestBudget_geometry hQ0)
  have hsum : productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) +
      (p + 2) ^ (max a b) + 1 + ell ≤ (p + 2) ^ C := by
    simpa [X, Y, Q, E, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbound p hp0
  have hR : (p + 2) ^ (max a b) + 1 ≤ (p + 2) ^ C := by
    linarith
  have hE : productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) ≤
      (p + 2) ^ C := by linarith
  have hellP : (ell : ℝ) ≤ (p + 2) ^ C := by linarith
  refine ⟨pow_le_pow_right₀ hbase (le_max_left _ _),
    pow_le_pow_right₀ hbase (le_max_right _ _), hR, hE, ?_⟩
  calc
    _ ≤ Real.exp (Real.log xi) := Real.exp_le_exp.mpr (by linarith)
    _ = xi := Real.exp_log hxi

end Erdos3

end

end OAI
