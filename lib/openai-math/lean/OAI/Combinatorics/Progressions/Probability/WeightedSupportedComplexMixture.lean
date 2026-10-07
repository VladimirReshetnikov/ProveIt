import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistCellSelection

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberComplexMean_zero (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : (p.fiberLaw F).weight r = 0) (f : X → ℂ) : p.fiberComplexMean F r f = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  calc
    ‖p.fiberComplexMean F r f‖ ≤ p.mean (fun x => ‖if F x = r then f x else 0‖) :=
      p.norm_complexMean_le_mean_norm _
    _ = p.fiberMean F r (fun x => ‖f x‖) := by
      unfold fiberMean
      apply congrArg p.mean
      funext x
      by_cases hx : F x = r <;> simp [hx]
    _ = 0 := p.fiberMean_zero F r hr _

theorem fiberComplexMean_condition_error (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (f : X → ℂ) {target : ℂ} {ε : ℝ}
    (he : ∀ hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)),
      ‖(p.condition _ hr).complexMean f - target‖ ≤ ε) :
    ‖p.fiberComplexMean F r f - ((p.fiberLaw F).weight r : ℂ) * target‖ ≤
      (p.fiberLaw F).weight r * ε := by
  by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
  · rw [p.fiberComplexMean_eq_condition F r f hr, p.fiberLaw_weight_eq_mass,
      ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left (he hr) (p.mass_nonneg _)
  · have hz : (p.fiberLaw F).weight r = 0 := by
      rw [p.fiberLaw_weight_eq_mass]
      exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
    rw [p.fiberComplexMean_zero F r hz f, hz]
    simp

theorem complexMean_supported_fiber_error (p : FiniteProbabilityWeights X) (F : X → R)
    (f : X → ℂ) (target : R → ℂ) {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ‖(p.condition _ hr).complexMean f - target r‖ ≤ ε) :
    ‖p.complexMean f - (p.fiberLaw F).complexMean target‖ ≤ ε := by
  have hsplit : p.complexMean f = ∑ r, p.fiberComplexMean F r f := by
    simpa only [Finset.mem_univ, ite_true] using
      (p.sum_fiberComplexMean_on F Finset.univ f).symm
  rw [hsplit, complexMean, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, (p.fiberLaw F).weight r * ε :=
      Finset.sum_le_sum (fun r _ => p.fiberComplexMean_condition_error F r f (he r))
    _ = ε := by rw [← Finset.sum_mul, (p.fiberLaw F).total, one_mul]

omit [Fintype R] in
theorem condition_complexMean_fiber_mul (p : FiniteProbabilityWeights X) (F : X → R)
    (r : R) (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)))
    (f : X → ℂ) (b : R → ℂ) :
    (p.condition _ hr).complexMean (fun x => b (F x) * f x) =
      b r * (p.condition _ hr).complexMean f := by
  refine ((p.condition _ hr).complexMean_congr_support ?_).trans
    ((p.condition _ hr).complexMean_mul_left (b r) f)
  intro x hx
  have hxr : F x = r := (Finset.mem_filter.mp (condition_weight_support p _ hr x hx).1).2
  rw [hxr]

theorem complexMean_supported_fiber_mul_error (p : FiniteProbabilityWeights X) (F : X → R)
    (f : X → ℂ) (target b : R → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ r, ‖b r‖ ≤ 1)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ‖(p.condition _ hr).complexMean f - target r‖ ≤ ε) :
    ‖p.complexMean (fun x => b (F x) * f x) -
      (p.fiberLaw F).complexMean (fun r => b r * target r)‖ ≤ ε := by
  apply p.complexMean_supported_fiber_error F
  intro r hr
  rw [p.condition_complexMean_fiber_mul F r hr f b, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left (he r hr) (norm_nonneg _)).trans
    ((mul_le_mul_of_nonneg_right (hb r) hε).trans_eq (one_mul ε))

omit [DecidableEq X] [Fintype R] [DecidableEq R] in
theorem toPMF_bind_scaled_complexMean {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (C : ℝ) (y : Y) :
    p.complexMean (fun x => ((C * (q x y).toReal : ℝ) : ℂ)) =
      ((C * ((p.toPMF.bind q) y).toReal : ℝ) : ℂ) := by
  simp only [complexMean, toPMF_bind_toReal, mean, Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem complexMean_supported_fiber_variable_error (p : FiniteProbabilityWeights X) (F : X → R)
    (f : X → ℂ) (target : R → ℂ) (error : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ‖(p.condition _ hr).complexMean f - target r‖ ≤ error r) :
    ‖p.complexMean f - (p.fiberLaw F).complexMean target‖ ≤ (p.fiberLaw F).mean error := by
  have hsplit : p.complexMean f = ∑ r, p.fiberComplexMean F r f := by
    simpa only [Finset.mem_univ, ite_true] using
      (p.sum_fiberComplexMean_on F Finset.univ f).symm
  rw [hsplit, complexMean, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun r _ => p.fiberComplexMean_condition_error F r f (he r)))

theorem complexMean_supported_fiber_weighted_error (p : FiniteProbabilityWeights X) (F : X → R)
    (f : X → ℂ) (target b : R → ℂ) {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ‖(p.condition _ hr).complexMean f - target r‖ ≤ ε) :
    ‖p.complexMean (fun x => b (F x) * f x) -
      (p.fiberLaw F).complexMean (fun r => b r * target r)‖ ≤
        ε * (p.fiberLaw F).mean (fun r => ‖b r‖) := by
  have h := p.complexMean_supported_fiber_variable_error F
    (fun x => b (F x) * f x) (fun r => b r * target r) (fun r => ‖b r‖ * ε) (by
      intro r hr
      rw [p.condition_complexMean_fiber_mul F r hr f b, ← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (he r hr) (norm_nonneg _))
  apply h.trans_eq
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end Erdos3.FiniteProbabilityWeights

end

end OAI
