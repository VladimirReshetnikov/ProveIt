import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_mul_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * g x) =
      (FiniteProbabilityWeights.pi μ).mean f * (FiniteProbabilityWeights.pi μ).mean g := by
  have hleft (x y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp only [productCoordinateMix, hi, ite_true]
  have hright (x y : ∀ i, X i) : g (productCoordinateMix S x y) = g y := by
    apply hg
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hST hs hi
    simp only [productCoordinateMix, hn, ite_false]
  rw [← productMean_coordinateMix μ S (fun x => f x * g x)]
  simp only [hleft, hright, FiniteProbabilityWeights.mean_const_mul, FiniteProbabilityWeights.mean_mul_const]

theorem productConditionalMean_mul_disjoint (S T R : Finset ι) (hST : Disjoint S T)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) (x : ∀ i, X i) :
    productConditionalMean μ R (fun y => f y * g y) x =
      productConditionalMean μ R f x * productConditionalMean μ R g x := by
  have hdep (U : Finset ι) (h : (∀ i, X i) → ℝ) (hh : ProductDependsOn U h) :
      ProductDependsOn U (fun y => h (productCoordinateMix R x y)) := by
    intro y z hyz
    apply hh
    intro i hi
    by_cases hr : i ∈ R
    · simp only [productCoordinateMix, hr, ite_true]
    · simp only [productCoordinateMix, hr, ite_false, hyz i hi]
  exact productMean_mul_disjoint μ S T hST _ _ (hdep S f hf) (hdep T g hg)

theorem productConditionalMean_union_irrelevant (S R T : Finset ι) (hST : Disjoint S T)
    (f : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f) (x : ∀ i, X i) :
    productConditionalMean μ (R ∪ T) f x = productConditionalMean μ R f x := by
  unfold productConditionalMean
  congr 1
  funext y
  apply hf
  intro i hi
  have hn : i ∉ T := fun ht => Finset.disjoint_left.mp hST hi ht
  simp only [productCoordinateMix, Finset.mem_union, hn, or_false]

end Erdos3

end

end OAI
