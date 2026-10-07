import OAI.Combinatorics.Progressions.Probability.WeightedSupportedComplexMixture

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R Y : Type*} [Fintype X] [DecidableEq X]
variable [Fintype R] [DecidableEq R] [Fintype Y]

theorem mean_norm_supported_fiber_error
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → R)
    (f : X → Y → ℂ) (target : R → Y → ℂ) (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      q.mean (fun y => ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖) ≤ ε r) :
    q.mean (fun y => ‖p.complexMean (fun x => f x y) -
      (p.fiberLaw F).complexMean (fun r => target r y)‖) ≤ (p.fiberLaw F).mean ε := by
  let D : R → Y → ℂ := fun r y => p.fiberComplexMean F r (fun x => f x y) -
    ((p.fiberLaw F).weight r : ℂ) * target r y
  have hsplit (y : Y) : p.complexMean (fun x => f x y) -
      (p.fiberLaw F).complexMean (fun r => target r y) = ∑ r, D r y := by
    have h := p.sum_fiberComplexMean_on F Finset.univ (fun x => f x y)
    simp only [Finset.mem_univ, ite_true] at h
    rw [← h, complexMean, ← Finset.sum_sub_distrib]
  have hcell (r : R) : q.mean (fun y => ‖D r y‖) ≤ (p.fiberLaw F).weight r * ε r := by
    by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
    · have hfactor (y : Y) : ‖D r y‖ = p.mass (Finset.univ.filter (fun x => F x = r)) *
          ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖ := by
        dsimp only [D]
        rw [p.fiberComplexMean_eq_condition F r _ hr, p.fiberLaw_weight_eq_mass,
          ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.mass_nonneg _)]
      simp_rw [hfactor]
      rw [p.fiberLaw_weight_eq_mass]
      calc
        _ = p.mass (Finset.univ.filter (fun x => F x = r)) *
            q.mean (fun y => ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖) := by
          simp only [mean, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (he r hr) (p.mass_nonneg _)
    · have hz : (p.fiberLaw F).weight r = 0 := by
        rw [p.fiberLaw_weight_eq_mass]
        exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
      simp only [D, p.fiberComplexMean_zero F r hz, hz, Complex.ofReal_zero,
        zero_mul, sub_self, norm_zero, q.mean_const, le_refl]
  calc
    _ = q.mean (fun y => ‖∑ r, D r y‖) := by simp only [hsplit]
    _ ≤ q.mean (fun y => ∑ r, ‖D r y‖) := q.mean_mono (fun y => norm_sum_le _ _)
    _ = ∑ r, q.mean (fun y => ‖D r y‖) := by
      simp only [mean, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ r, (p.fiberLaw F).weight r * ε r := Finset.sum_le_sum (fun r _ => hcell r)
    _ = _ := rfl

theorem mean_norm_supported_fiber_error_uniform
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → R)
    (f : X → Y → ℂ) (target : R → Y → ℂ) {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      q.mean (fun y => ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖) ≤ ε) :
    q.mean (fun y => ‖p.complexMean (fun x => f x y) -
      (p.fiberLaw F).complexMean (fun r => target r y)‖) ≤ ε := by
  simpa only [mean_const] using p.mean_norm_supported_fiber_error q F f target (fun _ => ε) he

theorem complexMean_supported_fiber_test_error
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → R)
    (f : X → Y → ℂ) (target : R → Y → ℂ) (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      q.mean (fun y => ‖(p.condition _ hr).complexMean (fun x => f x y) - target r y‖) ≤ ε r)
    (φ : Y → ℂ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ‖q.complexMean (fun y =>
      (p.complexMean (fun x => f x y) - (p.fiberLaw F).complexMean (fun r => target r y)) * φ y)‖ ≤
      (p.fiberLaw F).mean ε := by
  apply (q.norm_complexMean_le_mean_norm _).trans
  apply le_trans (q.mean_mono (fun y => ?_)) (p.mean_norm_supported_fiber_error q F f target ε he)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hφ y)

end Erdos3.FiniteProbabilityWeights

end

end OAI
