import OAI.Combinatorics.Progressions.Sampling.SmoothSplitSampling

namespace OAI

section

namespace Erdos3

theorem smoothSamplingScale_pos {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 0 < S := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  linarith

theorem shiftedSmoothSampleSum_bounds (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) :
    S / 2 ≤ shiftedSmoothSampleSum a S ∧ shiftedSmoothSampleSum a S ≤ 3 * S / 2 := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hS1 : 1 ≤ S := by linarith
  have hS0 := smoothSamplingScale_pos hS
  have he := shiftedSmoothSampleSum_error a hS1
  have hsmall : 4 * (probabilityProfileLipschitz : ℝ) / S ≤ 1 / 2 :=
    (div_le_iff₀ hS0).mpr (by linarith)
  have hb := abs_le.mp (he.trans hsmall)
  have hlo : (1 / 2 : ℝ) ≤ shiftedSmoothSampleSum a S / S := by linarith [hb.1]
  have hhi : shiftedSmoothSampleSum a S / S ≤ (3 / 2 : ℝ) := by linarith [hb.2]
  constructor
  · linarith [(le_div_iff₀ hS0).mp hlo]
  · linarith [(div_le_iff₀ hS0).mp hhi]

theorem shiftedSmoothCoefficientPMF_le (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) (k : ℤ) :
    (shiftedSmoothCoefficientPMF a S (smoothSamplingScale_pos hS)
      (shiftedSmoothSampleSum_pos a hS) k).toReal ≤ 2 / S := by
  rw [shiftedSmoothCoefficientPMF_apply]
  have hZ := shiftedSmoothSampleSum_pos a hS
  calc
    _ ≤ 1 / shiftedSmoothSampleSum a S :=
      div_le_div_of_nonneg_right (smoothProbabilityProfile_range _).2 hZ.le
    _ ≤ 2 / S := (div_le_div_iff₀ hZ (smoothSamplingScale_pos hS)).mpr
      (by linarith [(shiftedSmoothSampleSum_bounds a hS).1])

theorem shiftedSmoothCoefficientPMF_support (a : ℝ) {S : ℝ} (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) {k : ℤ}
    (hk : k ∈ (shiftedSmoothCoefficientPMF a S hS hZ).support) :
    |(k : ℝ) - a| < 3 * S / 4 := by
  by_contra! h
  have hz : smoothProbabilityProfile (((k : ℝ) - a) / S) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hS]
    apply (le_div_iff₀ hS).mpr
    linarith
  apply hk
  change ENNReal.ofReal (smoothProbabilityProfile (((k : ℝ) - a) / S) /
    shiftedSmoothSampleSum a S) = 0
  simp only [hz, zero_div, ENNReal.ofReal_zero]

end Erdos3

end

end OAI
