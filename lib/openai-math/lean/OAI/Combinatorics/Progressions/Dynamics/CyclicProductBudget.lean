import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation

namespace OAI

section

namespace Erdos3

def cyclicProductInputBudget (p : ℝ) : ℝ := productNiltestBudget p + 3 * p + 17

def cyclicProductVolumeBudget (p : ℝ) : ℝ := p ^ 2 + 3 * p + 16

def cyclicProductCutoffBudget (s c : ℕ) (p : ℝ) : ℝ :=
  ((s + 3) ^ (s + 3) : ℕ) + (s + 3 : ℕ) * cyclicProductVolumeBudget p +
    (2 ^ (s + 2) : ℕ) * (cyclicProductInputBudget p + c) ^ c

def cyclicProductDetectionBudget (s c : ℕ) (p : ℝ) : ℝ :=
  (2 ^ (s + 2) + 1 : ℕ) * (cyclicProductCutoffBudget s c p + 1) + 4

theorem cyclicProductInputBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ cyclicProductInputBudget p ∧ productNiltestBudget p ≤ cyclicProductInputBudget p ∧
      3 * p + 16 ≤ cyclicProductInputBudget p := by
  have hn : 0 ≤ productNiltestBudget p := (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp)
  unfold cyclicProductInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem cyclicProductCutoffBudget_nonneg (s c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ cyclicProductCutoffBudget s c p := by
  have hq := (cyclicProductInputBudget_bounds hp).1
  unfold cyclicProductCutoffBudget cyclicProductVolumeBudget
  positivity

theorem cyclic_product_retained_correlation (m : ℕ) {p : ℝ} (hm : (m : ℝ) ≤ p) :
    Real.exp (-(3 * p + 16)) ≤ Real.exp (-p) / (2 * ((m : ℝ) + 8)) := by
  have hd : 2 * ((m : ℝ) + 8) ≤ Real.exp (2 * p + 16) := by
    linarith [Real.add_one_le_exp (2 * p + 16)]
  calc
    _ = Real.exp (-p) / Real.exp (2 * p + 16) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hd

theorem cyclic_product_retained_volume (m : ℕ) {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) :
    Real.exp (-cyclicProductVolumeBudget p) ≤
      Real.exp (-p) / (2 * ((m : ℝ) + 8) * Real.exp ((m : ℝ) * p)) := by
  have hd : 2 * ((m : ℝ) + 8) ≤ Real.exp (2 * p + 16) := by
    linarith [Real.add_one_le_exp (2 * p + 16)]
  have he : Real.exp ((m : ℝ) * p) ≤ Real.exp (p ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hden : 2 * ((m : ℝ) + 8) * Real.exp ((m : ℝ) * p) ≤
      Real.exp (2 * p + 16 + p ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul hd he (Real.exp_nonneg _) (Real.exp_nonneg _)
  calc
    _ = Real.exp (-p) / Real.exp (2 * p + 16 + p ^ 2) := by
      rw [← Real.exp_sub]
      congr 1
      unfold cyclicProductVolumeBudget
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hden

theorem cyclic_product_cutoff_exponential (s c : ℕ) (p : ℝ) :
    Real.exp (-cyclicProductCutoffBudget s c p) ≤
      ((1 : ℝ) / ((s : ℝ) + 3) ^ (s + 3)) *
        Real.exp (-cyclicProductVolumeBudget p) ^ (s + 3) *
        Real.exp (-((cyclicProductInputBudget p + c) ^ c)) ^ (2 ^ (s + 2)) := by
  have hc : Real.exp (-(((s + 3) ^ (s + 3) : ℕ) : ℝ)) ≤
      (1 : ℝ) / ((s : ℝ) + 3) ^ (s + 3) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, mul_one, pow_one] using
      exp_neg_nat_mul_le_inverse_pow ((s + 3) ^ (s + 3)) 1 (by positivity) (p := 1) (by norm_num)
  calc
    _ = Real.exp (-(((s + 3) ^ (s + 3) : ℕ) : ℝ)) *
        Real.exp (-cyclicProductVolumeBudget p) ^ (s + 3) *
        Real.exp (-((cyclicProductInputBudget p + c) ^ c)) ^ (2 ^ (s + 2)) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold cyclicProductCutoffBudget
      ring
    _ ≤ _ := by gcongr

theorem cyclic_product_transfer_exponential (s c : ℕ) (p : ℝ) :
    Real.exp (-cyclicProductDetectionBudget s c p) ≤
      (Real.exp (-cyclicProductCutoffBudget s c p) / 2) ^ (2 ^ (s + 2) + 1) / 4 := by
  have h4 : Real.exp (-(4 : ℝ)) ≤ 1 / 4 := by
    simpa only [Nat.cast_ofNat, mul_one, pow_one] using
      exp_neg_nat_mul_le_inverse_pow 4 1 (by norm_num) (p := 1) (by norm_num)
  calc
    _ = Real.exp (-cyclicProductCutoffBudget s c p - 1) ^ (2 ^ (s + 2) + 1) * Real.exp (-4) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold cyclicProductDetectionBudget
      push_cast
      ring
    _ ≤ (Real.exp (-cyclicProductCutoffBudget s c p) / 2) ^ (2 ^ (s + 2) + 1) * (1 / 4) := by
      gcongr
      exact exp_sub_one_le_half_exp _
    _ = _ := by ring

theorem exists_cyclicProductDetectionBudget_bound (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → cyclicProductDetectionBudget s c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  let Q := B + 3 * X + 17
  let V := X ^ 2 + 3 * X + 16
  let R := Polynomial.C ((s + 3) ^ (s + 3)) + Polynomial.C (s + 3) * V +
    Polynomial.C (2 ^ (s + 2)) * (Q + Polynomial.C c) ^ c
  let P := Polynomial.C (2 ^ (s + 2) + 1) * (R + 1) + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, V, Q, B, X, Polynomial.eval₂_pow, cyclicProductDetectionBudget,
    cyclicProductCutoffBudget, cyclicProductInputBudget, cyclicProductVolumeBudget,
    productNiltestBudget, productObservableLipBudget] using hbound p hp

end Erdos3

end

end OAI
