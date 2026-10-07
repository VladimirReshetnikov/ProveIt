import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_exp_weighted_error_le
    {B C b q e : ℝ} (hC : 0 ≤ C)
    (hBbound : B ≤ Real.exp b) (hCbound : C ≤ Real.exp b)
    (he : 2 * b + q + Real.log 8 ≤ e) :
    B * (C * Real.exp (-e)) ≤ Real.exp (-q) / 8 := by
  have hprod : B * C ≤ Real.exp b * Real.exp b :=
    mul_le_mul hBbound hCbound hC (Real.exp_nonneg _)
  calc
    B * (C * Real.exp (-e)) = (B * C) * Real.exp (-e) := (mul_assoc _ _ _).symm
    _ ≤ (Real.exp b * Real.exp b) * Real.exp (-e) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Real.exp (2 * b - e) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-q - Real.log 8) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-q) / 8 := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 8)]

theorem finiteFreezing_exp_score_surplus
    {Bweight Bobs Lip b q e t scoreThreshold : ℝ}
    (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : Bweight ≤ Real.exp b) (hobs : Bobs ≤ Real.exp b)
    (hlip : Lip ≤ Real.exp b)
    (he : 2 * b + q + Real.log 8 ≤ e)
    (ht : 2 * b + q + Real.log 8 ≤ t)
    (hscore : Real.exp (-q) ≤ scoreThreshold) :
    Real.exp (-q) / 2 + Bweight * (Lip * Real.exp (-e)) +
      (Bweight * Bobs) * Real.exp (-t) < scoreThreshold := by
  have herror := finiteFreezing_exp_weighted_error_le hLip hweight hlip he
  have hdiscard := finiteFreezing_exp_weighted_error_le hBobs hweight hobs ht
  rw [← mul_assoc] at hdiscard
  have hpos := Real.exp_pos (-q)
  linarith

theorem finiteFreezing_exp_half_score_le {q recursionParameter : ℝ}
    (hparameter : q + Real.log 2 ≤ recursionParameter) :
    Real.exp (-recursionParameter) ≤ Real.exp (-q) / 2 := by
  calc
    _ ≤ Real.exp (-q - Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end Erdos3.VectorPolynomial

end

end OAI
