import DirectBFSModelForwardMap
import DirectBFSModelWordTransfer
import DirectBFSEdgeForward
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSModelForwardWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CleanGeometry
open DirectBFSConjugacyBase DirectBFSConjugacyLift DirectBFSModelForwardMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forward_ne_one (x : V) (hx : x<943) (hne : x≠1) : forward x≠1 := by
  obtain ⟨i,hi,he⟩ := bounded_standard 943 x hx
  intro h
  rw [he,forward_cast] at h
  have heq : rowMap.getD i 0=1 := by exact_mod_cast h
  have hf : rowForward ⟨i,hi⟩=rowForward ⟨1,by decide⟩ := by
    apply Fin.ext
    change rowMap.getD i 0=rowMap.getD 1 0
    rw [heq]
    decide
  have hi1 : i=1 := congrArg Fin.val (row_bijective.1 hf)
  apply hne
  rw [he,hi1]
  norm_num

theorem original_cast (f : CompactLocalWord.Quad → ℕ) (hf : f (0,0,0,0)=0) (j : Fin 943) :
    CompactLocalWord.field f (j.val:V)=(f (Compact943Data.row j):V) := by
  rw [CompactLocalWord.field_cast f hf]
  change ((f (original[j.val]?.getD (0,0,0,0))):V) = _
  rw [←Array.getD_eq_getD_getElem?,DirectBFSRowTransfer.original_row]

theorem direct_forward_cast (f : DirectBFSLocalWord.Quad → ℕ) (hf : f (0,0,0,0)=0) (j : Fin 943) :
    DirectBFSLocalWord.field f (forward (j.val:V))=(f (DirectBFSSymbolicKernel.row (rowForward j)):V) := by
  rw [forward_cast,DirectBFSLocalWord.field_cast f hf]
  change ((f (direct[(rowForward j).val]?.getD (0,0,0,0))):V) = _
  rw [←Array.getD_eq_getD_getElem?,DirectBFSRowTransfer.direct_row]

theorem transfer (b : V → V) (N s : V) (hw : CompactLocalWord.Word b N s) :
    DirectBFSLocalWord.Word (fun j => forward (b j)) N s := by
  refine ⟨hw.pos,?_,?_,?_,?_,?_⟩
  · intro j hj; exact forward_bound _ (hw.tile_lt j hj)
  · intro j hj; exact forward_ne_one _ (hw.tile_lt j hj) (hw.tile_ne j hj)
  · rw [hw.marker,forward_zero]
  · intro j hj k hk he
    obtain ⟨a,ha,hea⟩ := bounded_standard 943 (b j) (hw.tile_lt j hj)
    obtain ⟨c,hc,hec⟩ := bounded_standard 943 (b k) (hw.tile_lt k hk)
    let i : Fin 943 := ⟨a,ha⟩
    let l : Fin 943 := ⟨c,hc⟩
    have hed := hw.east j hj k hk he
    rw [hea,hec,original_cast _ rfl i,original_cast _ rfl l] at hed
    have hnat : (Compact943Data.row i).2.2.1=(Compact943Data.row l).1 := by exact_mod_cast hed
    rw [hea,hec,direct_forward_cast _ rfl i,direct_forward_cast _ rfl l]
    exact_mod_cast DirectBFSEdgeForward.horizontal i l hnat
  · intro j hj k hk he
    obtain ⟨a,ha,hea⟩ := bounded_standard 943 (b j) (hw.tile_lt j hj)
    obtain ⟨c,hc,hec⟩ := bounded_standard 943 (b k) (hw.tile_lt k hk)
    let i : Fin 943 := ⟨a,ha⟩
    let l : Fin 943 := ⟨c,hc⟩
    have hed := hw.south j hj k hk he
    rw [hea,hec,original_cast _ rfl i,original_cast _ rfl l] at hed
    have hnat : (Compact943Data.row i).2.2.2=(Compact943Data.row l).2.1 := by exact_mod_cast hed
    rw [hea,hec,direct_forward_cast _ rfl i,direct_forward_cast _ rfl l]
    exact_mod_cast DirectBFSEdgeForward.vertical i l hnat
#print axioms DirectBFSModelForwardWord.forward_ne_one
#print axioms DirectBFSModelForwardWord.original_cast
#print axioms DirectBFSModelForwardWord.direct_forward_cast
#print axioms DirectBFSModelForwardWord.transfer
end DirectBFSModelForwardWord
