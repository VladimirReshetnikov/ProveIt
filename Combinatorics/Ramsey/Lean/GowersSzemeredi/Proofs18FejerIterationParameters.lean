import GowersSzemeredi.Proofs18FejerInverseThresholdEnvelope

/-! This module keeps `fejerCubicDiscrepancyParameter_le_one`; the rest of the
development, with its description, is in `Proofs18FejerIterationParametersSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerCubicDiscrepancyParameter_le_one {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) : fejerCubicDiscrepancyParameter alpha ≤ 1 := by
  let a := fejerCubicLocalQuadraticParameter alpha
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  have ha1 : a ≤ 1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hm : fejerCubicLocalizedMassParameter alpha ≤ 1 := by
    unfold fejerCubicLocalizedMassParameter
    have h1 : (2 : Real) ^ (-(59 : Int)) * alpha ^ 2 ≤ 1 :=
      (mul_le_mul (by norm_num : (2 : Real) ^ (-(59 : Int)) ≤ 1)
        (pow_le_one₀ hα.le hαone) (by positivity) zero_le_one).trans (by norm_num)
    exact (mul_le_mul h1 (pow_le_one₀ (by positivity) (by linarith only [hαone]))
      (by positivity) zero_le_one).trans (by norm_num)
  have hq : quadraticDiscrepancyParameter a ≤ 1 := by
    unfold quadraticDiscrepancyParameter
    have h1 : (2 : Real) ^ (-(20 : Int)) * a ^ 2 ≤ 1 :=
      (mul_le_mul (by norm_num : (2 : Real) ^ (-(20 : Int)) ≤ 1)
        (pow_le_one₀ ha.le ha1) (by positivity) zero_le_one).trans (by norm_num)
    exact (mul_le_mul h1 (pow_le_one₀ (by positivity) (by linarith only [ha1]))
      (by positivity) zero_le_one).trans (by norm_num)
  change fejerCubicLocalizedMassParameter alpha * quadraticDiscrepancyParameter a / 2 ≤ 1
  have hp := mul_le_mul hm hq (by unfold quadraticDiscrepancyParameter; positivity) zero_le_one
  linarith only [hp]

end LeanProofs.GowersSzemeredi
