import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

theorem stepOne_linear_budget {p : ℝ} (hp : 0 ≤ p) :
    3 * p + 1 ≤ (p + 2) ^ 4 := by
  have hs : 3 * p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  exact hs.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 2 ≤ 4))

theorem stepOne_denominator_budget {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 4) :=
  (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr
    ((show p + 1 ≤ 3 * p + 1 by linarith).trans (stepOne_linear_budget hp)))

theorem stepOne_slow_budget {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) / (2 * (Real.exp (-p) / Real.exp p)) ≤ Real.exp ((p + 2) ^ 4) := by
  have hδ : 0 < Real.exp (-p) / Real.exp p := div_pos (Real.exp_pos _) (Real.exp_pos _)
  calc
    _ ≤ (⌈Real.exp p⌉₊ : ℝ) / (Real.exp (-p) / Real.exp p) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (by linarith)
    _ ≤ Real.exp (p + 1) / (Real.exp (-p) / Real.exp p) :=
      div_le_div_of_nonneg_right (ceil_exp_le_exp_add_one hp) hδ.le
    _ = Real.exp (3 * p + 1) := by
      rw [← Real.exp_sub, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (stepOne_linear_budget hp)

theorem stepOne_kernel_height_budget {p : ℝ} (hp : 0 ≤ p) :
    ((2 * ⌈Real.exp p⌉₊ ^ 2 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ Real.exp 1 * (Real.exp (p + 1)) ^ 2 := by
      apply mul_le_mul
      · have h := Real.add_one_le_exp (1 : ℝ)
        linarith only [h]
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hp) 2
      · positivity
      · positivity
    _ = Real.exp (2 * p + 3) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h : 2 * p + 3 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
      exact h.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 2 ≤ 4))

end Erdos3

end

end OAI
