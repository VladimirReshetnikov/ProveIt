import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productLaw_supported_of_singleton_marginals (w : (∀ i, X i) → ℝ)
    (hw : ∀ x, 0 ≤ w x) {η : ℝ}
    (he : ∀ i x,
      |productFiberMass w {i} x - productFiberMass (FiniteProbabilityWeights.pi μ).weight {i} x| ≤
        η * productFiberMass (FiniteProbabilityWeights.pi μ).weight {i} x) :
    ∀ x, (FiniteProbabilityWeights.pi μ).weight x = 0 → w x = 0 := by
  intro x hx
  change (∏ i, (μ i).weight (x i)) = 0 at hx
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hx
  have hbase : productFiberMass (FiniteProbabilityWeights.pi μ).weight {i} x = 0 := by
    unfold productFiberMass
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : ∀ j ∈ ({i} : Finset I), y j = x j
    · have hp : (FiniteProbabilityWeights.pi μ).weight y = 0 := by
        change (∏ j, (μ j).weight (y j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [hy i (Finset.mem_singleton_self i), hi]
      rw [hp, zero_mul]
    · simp only [productFiberIndicator, hy, ite_false, mul_zero]
  have h := he i x
  rw [hbase, sub_zero, mul_zero] at h
  exact le_antisymm ((weight_le_productFiberMass w hw {i} x).trans
    ((le_abs_self _).trans h)) (hw x)

end Erdos3

end

end OAI
