import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem sourceDetection_error_share {A E η : ℝ}
    (hE : A + 5 ≤ E) (hη : η ≤ Real.exp (-(A + 5))) :
    Real.exp (-(A + 1)) + (2 * Real.exp (-E) + η) ≤ Real.exp (-A) := by
  have h1 : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    have hp : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 : ℝ))
      (Real.exp_nonneg (-1))
    nlinarith
  have h5 : Real.exp (-5) ≤ (1 / 6 : ℝ) := by
    have hp : Real.exp (-5) * Real.exp 5 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (5 : ℝ))
      (Real.exp_nonneg (-5))
    nlinarith
  have hE' := Real.exp_le_exp.mpr (neg_le_neg hE)
  have hadd (c : ℝ) : Real.exp (-(A + c)) = Real.exp (-A) * Real.exp (-c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hadd 5] at hE' hη
  rw [hadd 1]
  have hc1 := mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (-A))
  have hc5 := mul_le_mul_of_nonneg_left h5 (Real.exp_nonneg (-A))
  linarith

end Erdos3

end

end OAI
