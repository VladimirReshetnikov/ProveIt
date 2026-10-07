import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem lowDegreeCoordinateSets_zero (I : Type*) [Fintype I] [DecidableEq I] :
    lowDegreeCoordinateSets I 0 = {∅} := by
  simp [lowDegreeCoordinateSets]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_of_weighted_eq (f g : (∀ i, X i) → ℝ)
    (he : ∀ y, (FiniteProbabilityWeights.pi μ).weight y * f y =
      (FiniteProbabilityWeights.pi μ).weight y * g y)
    (S : Finset I) (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    productConditionalMean μ S f x = productConditionalMean μ S g x := by
  have hp : 0 < (FiniteProbabilityWeights.pi μ).weight x :=
    lt_of_le_of_ne ((FiniteProbabilityWeights.pi μ).nonneg x) (Ne.symm hx)
  apply mul_left_cancel₀ (ne_of_gt (productFiberMass_pos (FiniteProbabilityWeights.pi μ) S x hp))
  calc
    _ = productFiberMass (fun y => (FiniteProbabilityWeights.pi μ).weight y * f y) S x :=
      productConditionalMean_fiber_identity μ S f x
    _ = productFiberMass (fun y => (FiniteProbabilityWeights.pi μ).weight y * g y) S x := by
      congr 1
      funext y
      exact he y
    _ = _ := (productConditionalMean_fiber_identity μ S g x).symm

theorem productANOVA_of_weighted_eq (f g : (∀ i, X i) → ℝ)
    (he : ∀ y, (FiniteProbabilityWeights.pi μ).weight y * f y =
      (FiniteProbabilityWeights.pi μ).weight y * g y)
    (S : Finset I) (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    productANOVA μ S f x = productANOVA μ S g x := by
  unfold productANOVA
  apply Finset.sum_congr rfl
  intro U _
  rw [productConditionalMean_of_weighted_eq μ f g he (S \ U) x hx]

theorem productANOVAEnergy_of_weighted_eq (f g : (∀ i, X i) → ℝ)
    (he : ∀ y, (FiniteProbabilityWeights.pi μ).weight y * f y =
      (FiniteProbabilityWeights.pi μ).weight y * g y) (D : Finset (Finset I)) :
    productANOVAEnergy μ D f = productANOVAEnergy μ D g := by
  unfold productANOVAEnergy
  apply Finset.sum_congr rfl
  intro S _
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  by_cases hx : (FiniteProbabilityWeights.pi μ).weight x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [productANOVA_of_weighted_eq μ f g he S x hx]

theorem productANOVA_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp [productANOVA, productConditionalMean_empty]

theorem productANOVAEnergy_zero (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I 0) f =
      ((FiniteProbabilityWeights.pi μ).mean f) ^ 2 := by
  rw [lowDegreeCoordinateSets_zero]
  simp only [productANOVAEnergy, Finset.sum_singleton, productANOVA_empty,
    FiniteProbabilityWeights.mean_const]

end Erdos3

end

end OAI
