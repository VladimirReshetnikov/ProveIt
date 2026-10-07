import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def commonExtractionParameter (p : ℝ) : ℝ := 3 * p + 3

def commonInitialParameter (p : ℝ) : ℝ := (commonExtractionParameter p + 2) ^ 3

theorem commonExtractionParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ commonExtractionParameter p ∧ 2 * p ≤ commonExtractionParameter p ∧
      1 ≤ commonExtractionParameter p ∧ commonExtractionParameter p ≤ commonInitialParameter p := by
  have hq : 1 ≤ commonExtractionParameter p + 2 := by
    unfold commonExtractionParameter
    linarith
  have hpow := pow_le_pow_right₀ hq (show 1 ≤ (3 : ℕ) by decide)
  simp only [pow_one] at hpow
  unfold commonInitialParameter
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold commonExtractionParameter; linarith
  · unfold commonExtractionParameter; linarith
  · unfold commonExtractionParameter; linarith
  · linarith

theorem commonExtractionParameter_products {p C M : ℝ} (hp : 0 ≤ p)
    (_hC : 0 ≤ C) (hCp : C ≤ Real.exp p) (hM : 0 ≤ M) (hMp : M ≤ Real.exp p)
    (δ l : ℕ) (hδ : (δ : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    max 2 (C * (M + M)) ≤ Real.exp (commonExtractionParameter p) ∧
      ((δ * l : ℕ) : ℝ) ≤ Real.exp (commonExtractionParameter p) := by
  have hq := commonExtractionParameter_controls hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  constructor
  · apply max_le (htwo.trans (Real.exp_le_exp.mpr hq.2.2.1))
    calc
      _ ≤ Real.exp p * (Real.exp p + Real.exp p) :=
        mul_le_mul hCp (add_le_add hMp hMp) (add_nonneg hM hM) (Real.exp_nonneg _)
      _ = 2 * (Real.exp p * Real.exp p) := by ring
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (1 + (p + p)) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold commonExtractionParameter; linarith)
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hδ hl (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq.2.1

theorem exists_commonInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      commonInitialParameter p + 1 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + 2) ^ 3 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := (3 * Polynomial.X + 3 + 2) ^ 3
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + 1 + (Q + 2) ^ 3 + (Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ commonInitialParameter p :=
    (hp.trans (commonExtractionParameter_controls hp).1).trans
      (commonExtractionParameter_controls hp).2.2.2
  have h2 : 0 ≤ (commonInitialParameter p + 2) ^ 3 := by positivity
  have hC : 0 ≤ (commonInitialParameter p + C) ^ C := by positivity
  have hsum : commonInitialParameter p + 1 + (commonInitialParameter p + 2) ^ 3 +
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, commonInitialParameter, commonExtractionParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
