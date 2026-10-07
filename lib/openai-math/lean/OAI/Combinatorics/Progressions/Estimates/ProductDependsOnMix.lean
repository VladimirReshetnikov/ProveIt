import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem ProductDependsOn.mix {S T : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn (S ∪ T) f) (z : ∀ i, X i) :
    ProductDependsOn T (fun x => f (productCoordinateMix S z x)) := by
  intro x y hxy
  apply hf
  intro i hi
  by_cases hs : i ∈ S
  · simp only [productCoordinateMix, hs, ite_true]
  · have ht : i ∈ T := (Finset.mem_union.mp hi).resolve_left hs
    simp only [productCoordinateMix, hs, ite_false, hxy i ht]

end Erdos3

end

end OAI
