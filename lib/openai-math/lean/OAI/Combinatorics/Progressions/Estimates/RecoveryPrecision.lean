import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

section

namespace Erdos3

theorem recovery_precision_bounds {r K ε : ℝ} (hr : 0 ≤ r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hinv : 1 / ε ≤ Real.exp K) :
    let δ := ε * Real.exp (-r)
    0 < δ ∧ δ ≤ ε ∧ δ ≤ Real.exp (-r) ∧
      Real.exp r * δ = ε ∧ 1 / δ ≤ Real.exp (K + r) := by
  dsimp only
  have hexp : Real.exp (-r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hr)
  refine ⟨mul_pos hε (Real.exp_pos _), ?_, ?_, ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hε.le
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hε1 (Real.exp_pos _).le
  · calc
      _ = ε * (Real.exp r * Real.exp (-r)) := by ring
      _ = ε := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  · calc
      1 / (ε * Real.exp (-r)) = (1 / ε) * Real.exp r := by
        simp only [one_div, Real.exp_neg, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      _ ≤ Real.exp K * Real.exp r := mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
      _ = _ := (Real.exp_add K r).symm

end Erdos3

end

end OAI
