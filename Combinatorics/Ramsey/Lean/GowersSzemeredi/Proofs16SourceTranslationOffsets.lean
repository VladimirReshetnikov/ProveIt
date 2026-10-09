import GowersSzemeredi.Proofs16CoherentIterationBudget

/-! Source maps built from pointwise translations have a bounded number
of offsets. Composition multiplies the number of possible offsets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def sourceTranslationOffsets {N : Nat} [NeZero N] (source : ZMod N → ZMod N) : Finset (ZMod N) :=
  Finset.univ.image (fun u => source u-u)

theorem sourceTranslationOffsets_id_card {N : Nat} [NeZero N] :
    (sourceTranslationOffsets (id : ZMod N → ZMod N)).card = 1 := by
  have he : sourceTranslationOffsets (id : ZMod N → ZMod N) = {0} := by
    ext v
    simp only [sourceTranslationOffsets,Finset.mem_image,Finset.mem_univ,true_and,id_eq,sub_self,Finset.mem_singleton]
    constructor
    · rintro ⟨u,h⟩; exact h.symm
    · intro h; exact ⟨0,h.symm⟩
  rw [he,Finset.card_singleton]

theorem sourceTranslationOffsets_row_card_le {N : Nat} [NeZero N]
    (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) :
    (sourceTranslationOffsets (fun u => t (color u)+u)).card ≤ 4 := by
  have hsub : sourceTranslationOffsets (fun u => t (color u)+u) ⊆ Finset.univ.image t := by
    intro v hv
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨color u,Finset.mem_univ _,by simp⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

theorem sourceTranslationOffsets_comp_card_le {N : Nat} [NeZero N]
    (f g : ZMod N → ZMod N) :
    (sourceTranslationOffsets (fun u => f (g u))).card ≤
      (sourceTranslationOffsets f).card*(sourceTranslationOffsets g).card := by
  have hsub : sourceTranslationOffsets (fun u => f (g u)) ⊆
      ((sourceTranslationOffsets f) ×ˢ (sourceTranslationOffsets g)).image (fun p => p.1+p.2) := by
    intro v hv
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨(f (g u)-g u,g u-u),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_image.mpr ⟨g u,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
    · ring
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_product]))

end LeanProofs.GowersSzemeredi
