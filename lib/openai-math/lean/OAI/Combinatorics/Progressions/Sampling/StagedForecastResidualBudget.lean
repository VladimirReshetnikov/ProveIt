import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem stagedForecastResidual_gain_lower
    {n : ℕ} {stageLog gainLog gain : ℝ}
    (hstage : (n : ℝ) + 1 ≤ Real.exp stageLog)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-(gainLog + stageLog)) ≤ gain / ((n : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  calc
    Real.exp (-(gainLog + stageLog)) * ((n : ℝ) + 1) ≤
        Real.exp (-(gainLog + stageLog)) * Real.exp stageLog :=
      mul_le_mul_of_nonneg_left hstage (Real.exp_pos _).le
    _ = Real.exp (-gainLog) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ gain := hgain

theorem stagedForecastResidual_sum_bound
    {Stage : Type*} [Fintype Stage] {gain : ℝ} (hgain : 0 ≤ gain) :
    (∑ _k : Stage, (gain / ((Fintype.card Stage : ℝ) + 1)) / 32) ≤ gain / 32 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hden : (Fintype.card Stage : ℝ) + 1 ≠ 0 := by positivity
  calc
    (Fintype.card Stage : ℝ) * (gain / ((Fintype.card Stage : ℝ) + 1) / 32) ≤
        ((Fintype.card Stage : ℝ) + 1) *
          (gain / ((Fintype.card Stage : ℝ) + 1) / 32) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = gain / 32 := by field_simp

theorem stagedForecastResidual_stageLog_bound (n : ℕ) :
    (n : ℝ) + 1 ≤ Real.exp ((n : ℝ) + 1) := by
  have h := Real.add_one_le_exp ((n : ℝ) + 1)
  linarith

end Erdos3

end

end OAI
