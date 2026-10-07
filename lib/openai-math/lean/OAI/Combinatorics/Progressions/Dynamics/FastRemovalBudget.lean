import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_fast_removal_factor_budget (s a cA cD : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p → ∀ (K : ℝ), 0 ≤ K → K ≤ Real.exp p →
      K * Real.exp ((p + cA) ^ cA) * K ≤ Real.exp ((p + C) ^ C) ∧
      K * (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) ≤
        Real.exp ((p + C) ^ C) := by
  let P : Polynomial ℕ := 2 * Polynomial.X + (Polynomial.X + Polynomial.C cA) ^ cA +
    (Polynomial.X + Polynomial.C cD) ^ cD + Polynomial.C (s + 1) + (Polynomial.X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp K hK hKp
  have hpoly : 2 * p + (p + cA) ^ cA + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a ≤
      (p + C) ^ C := by simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hAexp : 2 * p + (p + cA) ^ cA ≤ (p + C) ^ C := by
    have h1 : 0 ≤ (p + cD) ^ cD := by positivity
    have h2 : 0 ≤ (p + 2) ^ a := by positivity
    have h3 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hDexp : p + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a ≤ (p + C) ^ C := by
    have h1 : 0 ≤ (p + cA) ^ cA := by positivity
    linarith
  have hAfactor : K * Real.exp ((p + cA) ^ cA) * K ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + cA) ^ cA) * Real.exp p := by gcongr
      _ = Real.exp (2 * p + (p + cA) ^ cA) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hAexp
  have hstep : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (s + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (s + 1 : ℝ))
  have hDfactor : K * (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) ≤
      Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * (Real.exp ((p + cD) ^ cD) * (Real.exp (s + 1) * Real.exp ((p + 2) ^ a))) := by
        gcongr
      _ = Real.exp (p + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a) := by
        simp only [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hDexp
  exact ⟨hAfactor, hDfactor⟩

end Erdos3

end

end OAI
