import OAI.Combinatorics.Progressions.Estimates.ProductMeanPullback

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X : I → Type*} [∀ i, Fintype (X i)]

omit [Fintype I] [Fintype J] [∀ i, Fintype (X i)] in
theorem productCoordinateMix_embedding (e : J ↪ I) (S : Finset J) (x y : ∀ i, X i) :
    (fun j => productCoordinateMix (S.map e) x y (e j)) =
      productCoordinateMix S (fun j => x (e j)) (fun j => y (e j)) := by
  funext j
  by_cases hj : j ∈ S <;> simp [productCoordinateMix, hj]

theorem productConditionalMean_embedding (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ↪ I) (base : ∀ i, X i) (S : Finset J)
    (f : (∀ j, X (e j)) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ (S.map e) (fun y => f (fun j => y (e j))) x =
      productConditionalMean (fun j => μ (e j)) S f (fun j => x (e j)) := by
  simp only [productConditionalMean, productCoordinateMix_embedding]
  exact productMean_pullback μ e e.injective base
    (fun y => f (productCoordinateMix S (fun j => x (e j)) y))

end Erdos3

end

end OAI
