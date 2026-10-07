import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

section

namespace Erdos3

open Topology

theorem exists_continuous_image_factor {X Y Z : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] (E : X → Y) (hE : Continuous E) (f : X → Z) (hf : Continuous f)
    (hfactor : ∀ x y, E x = E y → f x = f y) :
    ∃ g : Set.range E → Z, Continuous g ∧ ∀ x, g (Set.rangeFactorization E x) = f x := by
  let e : C(X, Set.range E) := ⟨Set.rangeFactorization E, hE.rangeFactorization⟩
  have hq : IsQuotientMap e :=
    IsQuotientMap.of_surjective_continuous Set.rangeFactorization_surjective hE.rangeFactorization
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(X, Z)) e :=
    fun x y hxy => hfactor x y (congrArg Subtype.val hxy)
  let g := hq.lift ⟨f, hf⟩ hfac
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

end Erdos3

end

end OAI
