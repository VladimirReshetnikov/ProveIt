import OAI.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
import OAI.Combinatorics.Progressions.Estimates.ProductMeanPullback

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productTuplePoint_weight_ne_zero (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (v : ∀ j, X (a j)) (base : ∀ i, X i)
    (hb : (FiniteProbabilityWeights.pi μ).weight base ≠ 0)
    (hv : (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v ≠ 0) :
    (FiniteProbabilityWeights.pi μ).weight (productTuplePoint a ha v base) ≠ 0 := by
  change (∏ i, (μ i).weight (base i)) ≠ 0 at hb
  change (∏ j, (μ (a j)).weight (v j)) ≠ 0 at hv
  change (∏ i, (μ i).weight (productTuplePoint a ha v base i)) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  by_cases hi : i ∈ Finset.univ.image a
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    rw [productTuplePoint_apply]
    exact Finset.prod_ne_zero_iff.mp hv j (Finset.mem_univ j)
  · have he : productTuplePoint a ha v base i = base i := by
      simp only [productTuplePoint, productSubtypePoint, hi, dite_false]
    rw [he]
    exact Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ i)

theorem exists_positive_productTuplePoint (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (v : ∀ j, X (a j))
    (hv : (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v ≠ 0) :
    ∃ x : ∀ i, X i, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 ∧ ∀ j, x (a j) = v j := by
  obtain ⟨base, hb⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  exact ⟨productTuplePoint a ha v base, productTuplePoint_weight_ne_zero μ a ha v base hb hv,
    productTuplePoint_apply a ha v base⟩

end Erdos3

end

end OAI
