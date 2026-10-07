import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

variable {A R : Type*} [Fintype A] [Fintype R]

theorem supportMask_complexMean_difference
    (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights R)
    (source : A → ℂ) (target : R → ℂ) (c : ℂ)
    (hfix : ∀ a, c * source a = source a) :
    p.complexMean source - q.complexMean (fun r => c * target r) =
      c * (p.complexMean source - q.complexMean target) := by
  have hsource : c * p.complexMean source = p.complexMean source := by
    rw [← p.complexMean_mul_left]
    congr 1
    funext a
    exact hfix a
  rw [q.complexMean_mul_left, mul_sub, hsource]

theorem supportMask_complexMean_difference_norm
    (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights R)
    (source : A → ℂ) (target : R → ℂ) (c : ℂ)
    (hfix : ∀ a, c * source a = source a) (hc : ‖c‖ ≤ 1) :
    ‖p.complexMean source - q.complexMean (fun r => c * target r)‖ ≤
      ‖p.complexMean source - q.complexMean target‖ := by
  rw [supportMask_complexMean_difference p q source target c hfix, norm_mul]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)

theorem supportMask_weighted_complexMean_difference
    (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights R)
    (label : A → R) (weight : R → ℂ) (source : A → ℂ) (target : R → ℂ) (c : ℂ)
    (hfix : ∀ a, c * source a = source a) :
    p.complexMean (fun a => weight (label a) * source a) -
        q.complexMean (fun r => weight r * (c * target r)) =
      c * (p.complexMean (fun a => weight (label a) * source a) -
        q.complexMean (fun r => weight r * target r)) := by
  have hs (a : A) : c * (weight (label a) * source a) = weight (label a) * source a := by
    rw [mul_left_comm, hfix a]
  simpa only [mul_left_comm c] using supportMask_complexMean_difference p q
    (fun a => weight (label a) * source a) (fun r => weight r * target r) c hs

end Erdos3

end

end OAI
