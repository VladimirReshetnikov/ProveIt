import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_density_sum_sub_le {X : Type*} (s : Finset X)
    (D a b : X → ℝ) (φ : X → ℂ) {ε : ℝ}
    (hD : ∀ x ∈ s, 0 ≤ D x) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1)
    (hab : ∀ x ∈ s, |a x-b x| ≤ ε) :
    ‖(∑ x ∈ s, ((D x*a x : ℝ) : ℂ)*φ x) -
      (∑ x ∈ s, ((D x*b x : ℝ) : ℂ)*φ x)‖ ≤ ε*(∑ x ∈ s, D x) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  have heq : ((D x*a x : ℝ) : ℂ)*φ x-((D x*b x : ℝ) : ℂ)*φ x =
      ((D x*(a x-b x) : ℝ) : ℂ)*φ x := by push_cast; ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD x hx)]
  calc
    _ ≤ D x * |a x-b x| * 1 := mul_le_mul_of_nonneg_left (hφ x hx)
      (mul_nonneg (hD x hx) (abs_nonneg _))
    _ ≤ ε*D x := by
      rw [mul_one, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (hab x hx) (hD x hx)

theorem retained_weighted_density_test {Z X Y : Type*} [Fintype Z]
    (p : FiniteProbabilityWeights Z) (s : Z → Finset X) (grid : Z → Y)
    (D a b : Z → X → ℝ) (φ : Y → X → ℂ) {ε : ℝ}
    (hD : ∀ z, p.weight z ≠ 0 → ∀ x ∈ s z, 0 ≤ D z x)
    (hφ : ∀ z, p.weight z ≠ 0 → ∀ x ∈ s z, ‖φ (grid z) x‖ ≤ 1)
    (hab : ∀ z, p.weight z ≠ 0 → ∀ x ∈ s z, |a z x-b z x| ≤ ε) :
    ‖p.complexMean (fun z => ∑ x ∈ s z, ((D z x*a z x : ℝ) : ℂ)*φ (grid z) x) -
      p.complexMean (fun z => ∑ x ∈ s z, ((D z x*b z x : ℝ) : ℂ)*φ (grid z) x)‖ ≤
        ε*p.mean (fun z => ∑ x ∈ s z, D z x) := by
  have he := p.norm_complexMean_sub_le _ _ (fun z => ε*(∑ x ∈ s z, D z x))
    (fun z hz => norm_weighted_density_sum_sub_le (s z) (D z) (a z) (b z) (φ (grid z))
      (hD z hz) (hφ z hz) (hab z hz))
  convert he using 1
  unfold FiniteProbabilityWeights.mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem retained_weighted_density_test_of_mass {Z X Y : Type*} [Fintype Z]
    (p : FiniteProbabilityWeights Z) (s : Z → Finset X) (grid : Z → Y)
    (D a b : Z → X → ℝ) (φ : Y → X → ℂ) {ε M : ℝ} (hε : 0 ≤ ε)
    (hD : ∀ z, p.weight z ≠ 0 → ∀ x ∈ s z, 0 ≤ D z x)
    (hφ : ∀ z, p.weight z ≠ 0 → ∀ x ∈ s z, ‖φ (grid z) x‖ ≤ 1)
    (hab : ∀ z, p.weight z ≠ 0 → ∀ x ∈ s z, |a z x-b z x| ≤ ε)
    (hmass : p.mean (fun z => ∑ x ∈ s z, D z x) ≤ M) :
    ‖p.complexMean (fun z => ∑ x ∈ s z, ((D z x*a z x : ℝ) : ℂ)*φ (grid z) x) -
      p.complexMean (fun z => ∑ x ∈ s z, ((D z x*b z x : ℝ) : ℂ)*φ (grid z) x)‖ ≤ ε*M :=
  (retained_weighted_density_test p s grid D a b φ hD hφ hab).trans
    (mul_le_mul_of_nonneg_left hmass hε)

end Erdos3

end

end OAI
