import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem finiteOrderedSubset_sum (k : ℕ) (g : Finset I → ℝ) :
    (∑ a : Fin k → I, if StrictMono a then g (Finset.univ.image a) else 0) =
      ∑ S ∈ Finset.univ.powersetCard k, g S := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun a _ => Finset.univ.image a)
    (fun S hS => S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_of_injective Finset.univ hm.injective⟩
  · intro S hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (S.orderEmbOfFin _).strictMono⟩
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact (Finset.orderEmbOfFin_unique _ (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hm).symm
  · intro S hS
    exact Finset.image_orderEmbOfFin_univ S _
  · intro a _
    rfl

end Erdos3

end

end OAI
