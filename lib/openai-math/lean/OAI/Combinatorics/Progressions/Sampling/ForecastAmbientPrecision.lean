import OAI.Combinatorics.Progressions.Estimates.ModelTransferPrecision

namespace OAI

section

namespace Erdos3

theorem forecast_ambient_exp_error {δ M Q A E : ℝ}
    (hδ : δ ≤ Real.exp (-(E + 4))) (hM : M ≤ Real.exp Q)
    (hA : Q + E + 4 ≤ A) :
    2 * δ + M * Real.exp (-A) ≤ Real.exp (-E) := by
  have hterm : M * Real.exp (-A) ≤ Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-A) :=
        mul_le_mul_of_nonneg_right hM (Real.exp_nonneg _)
      _ = Real.exp (Q - A) := by rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp (-(E + 4)) := Real.exp_le_exp.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-(E + 4)) := by linarith
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
