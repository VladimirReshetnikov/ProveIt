import OAI.Combinatorics.Progressions.Estimates.ScalarDominatedSlack

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def joint (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (X × Y) where
  weight z := p.weight z.1 * (q z.1).weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) ((q z.1).nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, total, mul_one]

theorem joint_mean (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y)
    (f : X × Y → ℝ) :
    (p.joint q).mean f = p.mean (fun x => (q x).mean (fun y => f (x,y))) := by
  simp only [mean, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem joint_complexMean (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y)
    (f : X × Y → ℂ) :
    (p.joint q).complexMean f = p.complexMean (fun x => (q x).complexMean (fun y => f (x,y))) := by
  simp only [complexMean, joint, Fintype.sum_prod_type, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def centeredKernelMatrix (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) (x : X) (y : Y) : ℝ := (K x).weight y - ν.weight y

omit [Fintype X] in
theorem centeredKernelMatrix_apply (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) (f : Y → ℝ) (x : X) :
    (∑ y, centeredKernelMatrix ν K x y * f y) = (K x).mean f - ν.mean f := by
  simp only [centeredKernelMatrix, sub_mul, Finset.sum_sub_distrib, FiniteProbabilityWeights.mean]

theorem FiniteProbabilityWeights.mean_centered_sq (ν : FiniteProbabilityWeights Y) (f : Y → ℝ) :
    ν.mean (fun y => (f y - ν.mean f) ^ 2) = ν.mean (fun y => f y ^ 2) - (ν.mean f) ^ 2 := by
  calc
    _ = ν.mean (fun y => f y ^ 2 - (2 * ν.mean f) * f y + (ν.mean f) ^ 2) := by
      congr 1
      funext y
      ring
    _ = _ := by
      rw [ν.mean_add, ν.mean_sub, ν.mean_const_mul, ν.mean_const]
      ring

theorem centeredKernelMatrix_sq_le (μ : FiniteProbabilityWeights X) (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : Y → ℝ, ν.mean f = 0 →
      μ.mean (fun x => (K x).mean f ^ 2) ≤ C * ν.mean (fun y => f y ^ 2)) (f : Y → ℝ) :
    μ.mean (fun x => (∑ y, centeredKernelMatrix ν K x y * f y) ^ 2) ≤
      C * ν.mean (fun y => f y ^ 2) := by
  have hzero : ν.mean (fun y => f y - ν.mean f) = 0 := by
    rw [ν.mean_sub, ν.mean_const, sub_self]
  have hc := hbound (fun y => f y - ν.mean f) hzero
  have he (x : X) : (K x).mean (fun y => f y - ν.mean f) =
      ∑ y, centeredKernelMatrix ν K x y * f y := by
    rw [centeredKernelMatrix_apply, FiniteProbabilityWeights.mean_sub, FiniteProbabilityWeights.mean_const]
  simp_rw [he] at hc
  rw [ν.mean_centered_sq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hC)

end Erdos3

end

end OAI
