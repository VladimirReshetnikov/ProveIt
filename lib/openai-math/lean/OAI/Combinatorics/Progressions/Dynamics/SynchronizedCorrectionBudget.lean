import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exp_repeated_add_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.exp p + Real.exp p + Real.exp q ≤ Real.exp (p + q + 2) := by
  have hpq : Real.exp p ≤ Real.exp (p + q) := Real.exp_le_exp.mpr (le_add_of_nonneg_right hq)
  have hqp : Real.exp q ≤ Real.exp (p + q) := Real.exp_le_exp.mpr (le_add_of_nonneg_left hp)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ Real.exp (p + q) + Real.exp (p + q) + Real.exp (p + q) := add_le_add (add_le_add hpq hpq) hqp
    _ = 3 * Real.exp (p + q) := by ring
    _ ≤ Real.exp 2 * Real.exp (p + q) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_synchronizedCorrection_budget (a d r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a + p + (p + d) ^ d + 2 ≤ (p + C) ^ C ∧
      (p + r) ^ r ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X +
    (Polynomial.X + Polynomial.C d) ^ d + 2 + (Polynomial.X + Polynomial.C r) ^ r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hd : 0 ≤ (p + d) ^ d := by positivity
  have hr : 0 ≤ (p + r) ^ r := by positivity
  have hsum : (p + a) ^ a + p + (p + d) ^ d + 2 + (p + r) ^ r ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
