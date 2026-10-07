import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteMean_abs_sub_le {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (f g : Ω → ℝ) {ε : ℝ}
    (h : ∀ x, |f x-g x| ≤ ε) : |p.mean f-p.mean g| ≤ ε := by
  rw [FiniteProbabilityWeights.mean, FiniteProbabilityWeights.mean, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |p.weight x*f x-p.weight x*g x| := Finset.abs_sum_le_sum_abs _ _
    _ = p.mean (fun x => |f x-g x|) := by
      simp only [← mul_sub, abs_mul, abs_of_nonneg (p.nonneg _), FiniteProbabilityWeights.mean]
    _ ≤ p.mean (fun _ => ε) := p.mean_mono h
    _ = ε := p.mean_const ε

theorem finiteMean_masked_comparison {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (mass density : Ω → ℝ) {mask G ε η target : ℝ}
    (hm : 0 ≤ mask) (hG : mask ≤ G) (hη : 0 ≤ η)
    (hcoeff : ∀ x, |mass x-mask*density x| ≤ ε)
    (hquad : |p.mean density-target| ≤ η) :
    |p.mean mass-mask*target| ≤ ε+G*η := by
  have hmean : p.mean (fun x => mask*density x) = mask*p.mean density := by
    unfold FiniteProbabilityWeights.mean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h₁ := finiteMean_abs_sub_le p mass (fun x => mask*density x) hcoeff
  rw [hmean] at h₁
  have h₂ : |mask*p.mean density-mask*target| ≤ G*η := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hm]
    exact (mul_le_mul_of_nonneg_left hquad hm).trans (mul_le_mul_of_nonneg_right hG hη)
  exact (abs_sub_le _ _ _).trans (add_le_add h₁ h₂)

end Erdos3

end

end OAI
