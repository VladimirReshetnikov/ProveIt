import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem forecastResidualExponentialBudget
    {Bbranch gainLog E u gain : ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ Real.exp Bbranch)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hu : Bbranch + gainLog + E + 6 ≤ u) :
    (n : ℝ) * Real.exp (-u) / Real.exp (-E) ≤ gain / 32 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have h32 : (32 : ℝ) ≤ Real.exp 6 := by
    calc
      32 ≤ (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) htwo 6
      _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
  calc
    (n : ℝ) * Real.exp (-u) / Real.exp (-E) = (n : ℝ) * Real.exp (E - u) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring
    _ ≤ Real.exp Bbranch * Real.exp (E - u) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = Real.exp (Bbranch + E - u) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-gainLog - 6) := Real.exp_le_exp.mpr (by linarith only [hu])
    _ = Real.exp (-gainLog) / Real.exp 6 := Real.exp_sub _ _
    _ ≤ Real.exp (-gainLog) / 32 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h32
    _ ≤ gain / 32 := div_le_div_of_nonneg_right hgain (by norm_num)

end Erdos3

end

end OAI
