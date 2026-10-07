import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

theorem frozen_correlation_precision_error (P D : ℝ) (hD : 0 ≤ D)
    {N : ℕ} (hN : 0 < N) (hlarge : Real.exp (D + 2 * P + 40) ≤ N) :
    Real.exp D * Real.exp (-(D + 2 * P + 40)) +
      12 * Real.exp (-(D + 2 * P + 40)) + 6 / N ≤ Real.exp (-(2 * P)) / 2 := by
  let ε := Real.exp (-(2 * P) - 40)
  have he : 0 < ε := Real.exp_pos _
  have hprod : Real.exp D * Real.exp (-(D + 2 * P + 40)) = ε := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrho : Real.exp (-(D + 2 * P + 40)) ≤ ε := by
    apply Real.exp_le_exp.mpr
    linarith
  have hinv : 1 / (N : ℝ) ≤ Real.exp (-(D + 2 * P + 40)) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have h := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-(D + 2 * P + 40))).le
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h
  have h6 : 6 / (N : ℝ) ≤ 6 * Real.exp (-(D + 2 * P + 40)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 6)
  have h38 : (38 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have hexp : Real.exp (-(2 * P)) = Real.exp 40 * ε := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hprod, hexp]
  nlinarith [mul_le_mul_of_nonneg_right h38 he.le]

theorem frozen_witness_budget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    productNiltestBudget (raisedNiltestBudget p) ≤ productNiltestBudget (raisedNiltestBudget q) := by
  unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
  gcongr

theorem exists_frozen_correlation_budget (c b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let L := (P + c) ^ c + 2 * P + 40
      let Q := P + (L + b) ^ b + 2
      L ≤ (P + C) ^ C ∧
        productNiltestBudget (raisedNiltestBudget (P + Q + 2)) ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C c) ^ c + 2 * X + 40
  let Q := X + (L + Polynomial.C b) ^ b + 2
  let R := X + Q + 2
  let A := R + (R + 2) ^ 2 + 3
  let U := (A + 2) ^ 2 + A + (A + (A ^ 2 + A + 3) ^ 2) + A ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (L + U)
  refine ⟨C, hC, ?_⟩
  intro P hP L' Q'
  have hL : 0 ≤ L' := by dsimp only [L']; positivity
  have hU : 0 ≤ productNiltestBudget (raisedNiltestBudget (P + Q' + 2)) := by
    dsimp only [productNiltestBudget, productObservableLipBudget, raisedNiltestBudget, Q', L']
    positivity
  have htotal : L' + productNiltestBudget (raisedNiltestBudget (P + Q' + 2)) ≤ (P + C) ^ C := by
    simpa [X, L, Q, R, A, U, L', Q', Polynomial.eval₂_pow,
      productNiltestBudget, productObservableLipBudget, raisedNiltestBudget] using hbudget P hP
  exact ⟨by linarith only [htotal, hU], by linarith only [htotal, hL]⟩

end Erdos3

end

end OAI
