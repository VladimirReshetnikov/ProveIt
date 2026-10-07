import OAI.Combinatorics.Progressions.Geometry.BoxDetectionExponents

namespace OAI

section

namespace Erdos3

def cyclicCutoffBudget (s c : ℕ) (p : ℝ) : ℝ :=
  ((s + 3) ^ (s + 3) : ℕ) + (s + 3 : ℕ) * (2 * p + 8) +
    (2 ^ (s + 2) : ℕ) * (p + 8 + c) ^ c

def cyclicDetectionBudget (s c : ℕ) (p : ℝ) : ℝ :=
  (2 ^ (s + 2) + 1 : ℕ) * (cyclicCutoffBudget s c p + 1) + 4

theorem cyclicCutoffBudget_nonneg (s c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ cyclicCutoffBudget s c p := by
  unfold cyclicCutoffBudget
  positivity

theorem exists_cyclicDetectionBudget_bound (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → cyclicDetectionBudget s c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := Polynomial.C ((s + 3) ^ (s + 3)) + Polynomial.C (s + 3) * (2 * X + 8) +
    Polynomial.C (2 ^ (s + 2)) * (X + 8 + Polynomial.C c) ^ c
  let P := Polynomial.C (2 ^ (s + 2) + 1) * (R + 1) + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, X, Polynomial.eval₂_pow, cyclicDetectionBudget, cyclicCutoffBudget] using hbound p hp

theorem exp_sub_eight_le_eighth_exp (x : ℝ) : Real.exp (x - 8) ≤ Real.exp x / 8 := by
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  calc
    _ ≤ Real.exp (x - 8) * Real.exp 8 := mul_le_mul_of_nonneg_left h8 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem cyclic_retained_volume_exp (p : ℝ) :
    Real.exp (-(2 * p + 8)) ≤ Real.exp (-p) / (8 * Real.exp p) := by
  have h := div_le_div_of_nonneg_right (exp_sub_eight_le_eighth_exp (-p)) (Real.exp_nonneg p)
  calc
    _ = Real.exp (-p - 8) / Real.exp p := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := by simpa only [div_div] using h

theorem cyclic_cutoff_exponential_product (s c : ℕ) (p : ℝ) :
    Real.exp (-cyclicCutoffBudget s c p) ≤
      ((1 : ℝ) / ((s : ℝ) + 3) ^ (s + 3)) *
        Real.exp (-(2 * p + 8)) ^ (s + 3) *
        Real.exp (-((p + 8 + c) ^ c)) ^ (2 ^ (s + 2)) := by
  have hc : Real.exp (-(((s + 3) ^ (s + 3) : ℕ) : ℝ)) ≤
      (1 : ℝ) / ((s : ℝ) + 3) ^ (s + 3) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, mul_one, pow_one] using
      exp_neg_nat_mul_le_inverse_pow ((s + 3) ^ (s + 3)) 1 (by positivity) (p := 1) (by norm_num)
  calc
    _ = Real.exp (-(((s + 3) ^ (s + 3) : ℕ) : ℝ)) *
        Real.exp (-(2 * p + 8)) ^ (s + 3) *
        Real.exp (-((p + 8 + c) ^ c)) ^ (2 ^ (s + 2)) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold cyclicCutoffBudget
      ring
    _ ≤ _ := by gcongr

theorem cyclic_transfer_exponential (s c : ℕ) (p : ℝ) :
    Real.exp (-cyclicDetectionBudget s c p) ≤
      (Real.exp (-cyclicCutoffBudget s c p) / 2) ^ (2 ^ (s + 2) + 1) / 4 := by
  have h4 : Real.exp (-(4 : ℝ)) ≤ 1 / 4 := by
    simpa only [Nat.cast_ofNat, mul_one, pow_one] using
      exp_neg_nat_mul_le_inverse_pow 4 1 (by norm_num) (p := 1) (by norm_num)
  calc
    _ = Real.exp (-cyclicCutoffBudget s c p - 1) ^ (2 ^ (s + 2) + 1) * Real.exp (-4) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold cyclicDetectionBudget
      push_cast
      ring
    _ ≤ (Real.exp (-cyclicCutoffBudget s c p) / 2) ^ (2 ^ (s + 2) + 1) * (1 / 4) := by
      gcongr
      exact exp_sub_one_le_half_exp _
    _ = _ := by ring

end Erdos3

end

end OAI
