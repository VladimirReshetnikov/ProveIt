import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem refiltered_expansion_error_budget {cost metric ε R : ℝ}
    (hc : 0 ≤ cost) (hm : 0 ≤ metric) (hε : 0 ≤ ε)
    (hbudget : cost + metric + 10 ≤ R) :
    Real.exp cost * (Real.exp metric + 2) * ε + 6 * ε ≤ Real.exp R * ε := by
  have hE : 1 ≤ Real.exp cost := Real.one_le_exp hc
  have hK : 1 ≤ Real.exp metric := Real.one_le_exp hm
  have hEK : 1 ≤ Real.exp cost * Real.exp metric := by nlinarith
  have hEE : Real.exp cost ≤ Real.exp cost * Real.exp metric := by nlinarith [Real.exp_pos cost]
  have hsmall : Real.exp cost * (Real.exp metric + 2) + 6 ≤
      9 * (Real.exp cost * Real.exp metric) := by nlinarith
  have h9 : (9 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have hlarge : Real.exp cost * (Real.exp metric + 2) + 6 ≤ Real.exp R := by
    calc
      _ ≤ 9 * (Real.exp cost * Real.exp metric) := hsmall
      _ ≤ Real.exp 10 * (Real.exp cost * Real.exp metric) :=
        mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = Real.exp (cost + metric + 10) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hbudget
  nlinarith [mul_le_mul_of_nonneg_right hlarge hε]

end Erdos3

end

end OAI
