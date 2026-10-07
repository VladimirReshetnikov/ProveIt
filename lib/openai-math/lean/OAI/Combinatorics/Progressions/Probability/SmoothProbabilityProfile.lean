import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OAI.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

noncomputable def probabilityProfileBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

noncomputable def smoothProbabilityProfile : ℝ → ℝ :=
  probabilityProfileBump.normed volume

theorem smoothProbabilityProfile_contDiff : ContDiff ℝ ∞ smoothProbabilityProfile :=
  probabilityProfileBump.contDiff_normed

theorem smoothProbabilityProfile_compact : HasCompactSupport smoothProbabilityProfile :=
  probabilityProfileBump.hasCompactSupport_normed

theorem smoothProbabilityProfile_range (x : ℝ) :
    0 ≤ smoothProbabilityProfile x ∧ smoothProbabilityProfile x ≤ 1 := by
  refine ⟨probabilityProfileBump.nonneg_normed x, ?_⟩
  have h := probabilityProfileBump.normed_le_div_measure_closedBall_rIn volume x
  norm_num [probabilityProfileBump] at h
  exact h

theorem smoothProbabilityProfile_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) :
    smoothProbabilityProfile x = 0 := by
  have h : probabilityProfileBump x = 0 := probabilityProfileBump.zero_of_le_dist
    (by simpa only [probabilityProfileBump, Real.dist_eq, sub_zero] using hx)
  simp only [smoothProbabilityProfile, ContDiffBump.normed_def, h, zero_div]

theorem smoothProbabilityProfile_zero_outside (x : ℝ) (hx : 1 < |x|) :
    smoothProbabilityProfile x = 0 :=
  smoothProbabilityProfile_zero x (by linarith)

theorem smoothProbabilityProfile_integral : (∫ x, smoothProbabilityProfile x) = 1 :=
  probabilityProfileBump.integral_normed

theorem smoothProbabilityProfile_pos_zero : 0 < smoothProbabilityProfile 0 := by
  have h : probabilityProfileBump 0 = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simp [probabilityProfileBump])
  change 0 < probabilityProfileBump 0 / ∫ x, probabilityProfileBump x
  rw [h]
  exact one_div_pos.mpr probabilityProfileBump.integral_pos

theorem exists_smoothProbabilityProfile_lipschitz :
    ∃ A : ℝ≥0, 1 ≤ A ∧ LipschitzWith A smoothProbabilityProfile := by
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    smoothProbabilityProfile_compact (smoothProbabilityProfile_contDiff.of_le (by simp) :
      ContDiff ℝ 1 smoothProbabilityProfile) one_ne_zero
  exact ⟨A + 1, by simp, hA.weaken (by simp)⟩

noncomputable def probabilityProfileLipschitz : ℝ≥0 :=
  exists_smoothProbabilityProfile_lipschitz.choose

theorem probabilityProfileLipschitz_one_le : 1 ≤ probabilityProfileLipschitz :=
  exists_smoothProbabilityProfile_lipschitz.choose_spec.1

theorem smoothProbabilityProfile_lipschitz :
    LipschitzWith probabilityProfileLipschitz smoothProbabilityProfile :=
  exists_smoothProbabilityProfile_lipschitz.choose_spec.2

end Erdos3

end

end OAI
