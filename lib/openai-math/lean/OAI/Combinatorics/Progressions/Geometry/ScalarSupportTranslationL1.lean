import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalar_translation_l1_of_support (f : ℝ → ℝ) (c a b : ℝ) {w D : ℝ}
    (hw : 0 ≤ w) (hD : 0 ≤ D) (hs : ∀ x, w < |x - c| → f x = 0)
    (he : ∀ x, |f (x + a) - f (x + b)| ≤ D) :
    (∫ x, |f (x + a) - f (x + b)|) ≤ 4 * w * D := by
  let u := fun z => (Metric.closedBall (c - z) w).indicator (fun _ : ℝ => D)
  have hi (z : ℝ) : Integrable (u z) :=
    (integrableOn_const (isCompact_closedBall (c - z) w).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hz (z x : ℝ) (hx : x ∉ Metric.closedBall (c - z) w) : f (x + z) = 0 := by
    apply hs
    have hd : w < |x - (c - z)| := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, not_le] using hx
    have harg : x + z - c = x - (c - z) := by ring
    rwa [harg]
  have hb (x : ℝ) : |f (x + a) - f (x + b)| ≤ u a x + u b x := by
    by_cases ha : x ∈ Metric.closedBall (c - a) w <;>
      by_cases hb : x ∈ Metric.closedBall (c - b) w
    · simp only [u, Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      linarith [he x]
    · simpa only [u, Set.indicator_of_mem ha, Set.indicator_of_notMem hb, add_zero] using he x
    · simpa only [u, Set.indicator_of_notMem ha, Set.indicator_of_mem hb, zero_add] using he x
    · simp only [u, Set.indicator_of_notMem ha, Set.indicator_of_notMem hb,
        hz a x ha, hz b x hb, sub_self, abs_zero, add_zero, le_refl]
  calc
    _ ≤ ∫ x, u a x + u b x := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => abs_nonneg _)) ((hi a).add (hi b))
      (Filter.Eventually.of_forall hb)
    _ = _ := by
      rw [integral_add (hi a) (hi b)]
      simp only [u, integral_indicator_const D measurableSet_closedBall,
        Real.volume_real_closedBall hw, smul_eq_mul]
      ring

theorem affineProbabilityProfile_translation_l1 (c a b : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ x, |affineProbabilityProfile c w (x + a) - affineProbabilityProfile c w (x + b)|) ≤
      (4 * (probabilityProfileLipschitz : ℝ) / w) * |a - b| := by
  let D := w⁻¹ * (probabilityProfileLipschitz : ℝ) * (|a - b| / w)
  have he (x : ℝ) : |affineProbabilityProfile c w (x + a) -
      affineProbabilityProfile c w (x + b)| ≤ D := by
    rw [affineProbabilityProfile, affineProbabilityProfile, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hw)]
    have h := smoothProbabilityProfile_lipschitz.norm_sub_le ((x + a - c) / w) ((x + b - c) / w)
    have hd : (x + a - c) / w - (x + b - c) / w = (a - b) / w := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hd, abs_div, abs_of_pos hw] at h
    exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hw.le)).trans_eq (by dsimp [D]; ring)
  have h := scalar_translation_l1_of_support (affineProbabilityProfile c w) c a b hw.le
    (show 0 ≤ D by dsimp [D]; positivity) (affineProbabilityProfile_zero c hw) he
  refine h.trans_eq ?_
  dsimp [D]
  field_simp [hw.ne']

end Erdos3

end

end OAI
