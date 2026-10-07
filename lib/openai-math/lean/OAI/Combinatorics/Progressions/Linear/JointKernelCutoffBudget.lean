import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI


namespace Erdos3

noncomputable def jointKernelCutoff (n b : ℕ) (K T ε κ : ℝ) : ℕ :=
  ⌈1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε⌉₊

theorem jointKernelCutoff_bounds (n b : ℕ) {K T ε κ : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) :
    0 < jointKernelCutoff n b K T ε κ ∧
    n ≤ jointKernelCutoff n b K T ε κ ∧
    b ≤ jointKernelCutoff n b K T ε κ ∧
    1 / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    K / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    2 * T / ε ≤ (jointKernelCutoff n b K T ε κ : ℝ) := by
  have h1 : 0 < 1 / κ := one_div_pos.mpr hκ
  have h2 : 0 ≤ K / κ := div_nonneg hK hκ.le
  have h3 : 0 ≤ 2 * T / ε := div_nonneg (by positivity) hε.le
  have hc := Nat.le_ceil (1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε)
  change 1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε ≤
    (jointKernelCutoff n b K T ε κ : ℝ) at hc
  rw [add_div] at hc
  have hn : (n : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hb : (b : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hp : (0 : ℝ) < jointKernelCutoff n b K T ε κ := by
    have := Nat.cast_nonneg n (α := ℝ)
    have := Nat.cast_nonneg b (α := ℝ)
    linarith
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hn, by exact_mod_cast hb,
    by linarith, by linarith, by linarith⟩

theorem jointKernelCutoff_le (n b : ℕ) {K T ε κ : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) :
    (jointKernelCutoff n b K T ε κ : ℝ) ≤
      2 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε := by
  unfold jointKernelCutoff
  have h := Nat.ceil_lt_add_one
    (show 0 ≤ 1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε by positivity)
  linarith


theorem jointKernelCutoff_le_exp (n b : ℕ) {K T ε κ P : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) (hP : 0 ≤ P)
    (hnP : (n : ℝ) ≤ Real.exp P) (hbP : (b : ℝ) ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hTP : T ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) (hκP : κ⁻¹ ≤ Real.exp P) :
    (jointKernelCutoff n b K T ε κ : ℝ) ≤ Real.exp (2 * P + 8) := by
  have hE : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 2 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε := jointKernelCutoff_le n b hK hT hε hκ
    _ ≤ 2 + Real.exp P + Real.exp P + (1 + Real.exp P) * Real.exp P +
        2 * Real.exp P * Real.exp P := by
      simp only [div_eq_mul_inv]
      gcongr
    _ ≤ 8 * (Real.exp P) ^ 2 := by nlinarith [sq_nonneg (Real.exp P - 1)]
    _ ≤ Real.exp 8 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
    _ = Real.exp (2 * P + 8) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

end Erdos3

end OAI
