import Mathlib

namespace OAI

section

namespace Erdos3

theorem nativeLocalPivotVertical_inverse_precision_le_exp
    {pLocal r q : ℝ} (hbudget : pLocal + r + 1 ≤ q) :
    (Real.exp (-pLocal) * Real.exp (-r) / 2)⁻¹ ≤ Real.exp q := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hinv : (Real.exp (-pLocal) * Real.exp (-r) / 2)⁻¹ =
      2 * Real.exp (pLocal + r) := by
    rw [← Real.exp_add, ← neg_add, Real.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  rw [hinv]
  calc
    2 * Real.exp (pLocal + r) ≤ Real.exp 1 * Real.exp (pLocal + r) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (1 + (pLocal + r)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp q := Real.exp_le_exp.mpr (by linarith)

theorem nativeLocalPivotVertical_restore_correlation
    {c delta B x : ℝ} (hc : 0 < c)
    (h : c * delta / (2 * Real.exp B) ≤ c * x) :
    delta / (2 * Real.exp B) ≤ x := by
  rw [mul_div_assoc] at h
  nlinarith

end Erdos3

end

end OAI
