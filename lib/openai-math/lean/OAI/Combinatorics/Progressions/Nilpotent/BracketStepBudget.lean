import OAI.Combinatorics.Progressions.Dynamics.CurrentLayerBudget

namespace OAI

section

namespace Erdos3

def bracketConstructionBudget (p : ℝ) : ℝ := (p + 2) ^ 3 + 3 * p + 2

def bracketCorrectionBudget (p : ℝ) : ℝ :=
  (bracketConstructionBudget p + 2) ^ 36 + (bracketConstructionBudget p + 2) ^ 18 +
    bracketConstructionBudget p + (p + 2) ^ 3 + 2 * p + 1

theorem bracketConstructionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketConstructionBudget p := by unfold bracketConstructionBudget; positivity

theorem bracketCorrectionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketCorrectionBudget p := by
  have hq := bracketConstructionBudget_nonneg hp
  unfold bracketCorrectionBudget
  positivity

theorem bracket_construction_budget_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ bracketConstructionBudget p ∧ (p + 2) ^ 2 ≤ bracketConstructionBudget p ∧
      (p + 2) ^ 3 + p ≤ bracketConstructionBudget p ∧
      3 * p + 1 ≤ bracketConstructionBudget p := by
  have hc : 0 ≤ (p + 2) ^ 3 := by positivity
  have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 3 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 2 ≤ 3)
  unfold bracketConstructionBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem bracket_correction_budget_bounds {p : ℝ} (hp : 0 ≤ p)
    (n J D : ℕ) (hn : (n : ℝ) ≤ p) (hJ : (J : ℝ) ≤ Real.exp p)
    (hD : (D : ℝ) ≤ Real.exp ((p + 2) ^ 3)) :
    (((n : ℝ) + 1) * (J + 1)) *
        Real.exp ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p) ≤
        Real.exp (bracketCorrectionBudget p) ∧
      (D : ℝ) * Real.exp ((bracketConstructionBudget p + 2) ^ 36) ≤
        Real.exp (bracketCorrectionBudget p) := by
  have hq := bracketConstructionBudget_nonneg hp
  have h36 : 0 ≤ (bracketConstructionBudget p + 2) ^ 36 := by positivity
  have h18 : 0 ≤ (bracketConstructionBudget p + 2) ^ 18 := by positivity
  have h3 : 0 ≤ (p + 2) ^ 3 := by positivity
  constructor
  · calc
      _ ≤ Real.exp (2 * p + 1) *
          Real.exp ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p) :=
        mul_le_mul_of_nonneg_right (current_layer_coordinate_factor_bound hp n J hn hJ)
          (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 1 +
          ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p)) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold bracketCorrectionBudget; linarith
  · calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp ((bracketConstructionBudget p + 2) ^ 36) :=
        mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + (bracketConstructionBudget p + 2) ^ 36) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold bracketCorrectionBudget; linarith

theorem exists_bracket_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (bracketConstructionBudget p) + bracketCorrectionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 2
  let B : Polynomial ℕ := (Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1 +
    ((Q + 2) ^ 36 + (Q + 2) ^ 18 + Q + (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [B, Q, separationBudget, bracketCorrectionBudget, bracketConstructionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
