import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_initial_removal_budget (cS cR : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let A := (p + cS) ^ cS
      let B := (p + cR) ^ cR
      let r := p + 1 + 2 * A
      Real.exp A * Real.exp p ≤ Real.exp r ∧
      Real.exp A * (Real.exp p + Real.exp A) ≤ Real.exp r ∧
      Real.exp p * Real.exp r ≤ Real.exp ((p + C) ^ C) ∧
      Real.exp p * Real.exp B ≤ Real.exp ((p + C) ^ C) := by
  let P : Polynomial ℕ := 2 * Polynomial.X + 1 +
    2 * (Polynomial.X + Polynomial.C cS) ^ cS +
    (Polynomial.X + Polynomial.C cR) ^ cR
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp A B r
  have hA : 0 ≤ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hB : 0 ≤ B := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hpoly : 2 * p + 1 + 2 * A + B ≤ (p + C) ^ C := by
    simpa [P, A, B, Polynomial.eval₂_pow] using hbudget p hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hsmall : Real.exp A * (Real.exp p + Real.exp A) ≤ Real.exp r := by
    calc
      _ ≤ Real.exp A * (Real.exp (p + A) + Real.exp (p + A)) := by
        gcongr <;> linarith
      _ = 2 * Real.exp (p + 2 * A) := by
        rw [← two_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp 1 * Real.exp (p + 2 * A) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp r := by rw [← Real.exp_add]; congr 1; dsimp [r]; ring
  refine ⟨?_, hsmall, ?_, ?_⟩
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
