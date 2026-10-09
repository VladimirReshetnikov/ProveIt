import GowersSzemeredi.Proofs16FreimanFiniteSums

/-! Every translated proper progression is covered by 16^rank cells.
Every order-two Freiman map on the progression is order eight on each
cell; the cells depend only on the progression, not on the map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open OAI.Erdos3.BohrProgression

def translatedProgressionCell {N : Nat} (P : CyclicCenteredGAP N) (t : ZMod N)
    (c : Fin P.rank → Fin 16) : Finset (ZMod N) :=
  (Finset.univ.filter fun u : P.Param => progressionCellCode P u = c).image (fun u => t+P.eval u)

theorem translatedProgressionCell_subset {N : Nat} (P : CyclicCenteredGAP N) (t : ZMod N)
    (c : Fin P.rank → Fin 16) : translatedProgressionCell P t c ⊆ translatedFreimanDomain P.carrier t := by
  intro x hx
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨P.eval u,Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩,rfl⟩

theorem translatedProgressionCells_cover {N : Nat} (P : CyclicCenteredGAP N) (t : ZMod N) :
    Finset.univ.biUnion (translatedProgressionCell P t) = translatedFreimanDomain P.carrier t := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hx
    exact translatedProgressionCell_subset P t c hc
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨progressionCellCode P u,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩⟩

theorem translatedProgressionCell_freiman_eight {N : Nat} [NeZero N]
    (P : CyclicCenteredGAP N) (hP : P.Proper) (t : ZMod N) (f : ZMod N → ZMod N)
    (hf : FreimanHom 2 (translatedFreimanDomain P.carrier t) f) (c : Fin P.rank → Fin 16) :
    FreimanHom 8 (translatedProgressionCell P t c) f := by
  apply freimanHom_of_fin_sums
  intro x y hx hy he
  have hxu (j : Fin 8) : ∃ u : P.Param, progressionCellCode P u = c ∧ t+P.eval u = x j := by
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp (hx j)
    exact ⟨u,(Finset.mem_filter.mp hu).2,he⟩
  have hyv (j : Fin 8) : ∃ v : P.Param, progressionCellCode P v = c ∧ t+P.eval v = y j := by
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp (hy j)
    exact ⟨v,(Finset.mem_filter.mp hv).2,he⟩
  choose u huc hux using hxu
  choose v hvc hvy using hyv
  have h := progression_cell_eight_sum P hP t f hf u v
    (fun j => (huc j).trans (hvc j).symm) (by simpa only [hux,hvy] using he)
  simpa only [hux,hvy] using h

end LeanProofs.GowersSzemeredi
