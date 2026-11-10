import DiophantineConsistency.BFS943.DirectBFSModelIndexMap
import DiophantineConsistency.BFS943.Trace75BFSLocalWord
import DiophantineConsistency.BFS943.DirectBFSEdgeReflection
import DiophantineConsistency.Compact44.CleanGeometry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSModelWordTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CleanGeometry ArithmeticPackingBlocks
open DirectBFSConjugacyBase DirectBFSConjugacyLift DirectBFSModelIndexMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem back_ne_one (x : V) (hx : x<943) (hne : x≠1) : back x≠1 := by
  obtain ⟨i,hi,he⟩ := bounded_standard 943 x hx
  intro h
  rw [he,back_cast] at h
  have heq : rowInverse.getD i 0=1 := by exact_mod_cast h
  have hinv := row_inverse hi
  rw [heq] at hinv
  have hfixed : rowMap.getD 1 0=1 := by decide
  rw [hfixed] at hinv
  apply hne
  rw [he,←hinv]
  norm_num

theorem direct_cast (f : Trace75BFSLocalWord.Quad → ℕ) (hf : f (0,0,0,0)=0) (j : Fin 943) :
    Trace75BFSLocalWord.field f (j.val:V)=(f (DirectBFSSymbolicKernel.row j):V) := by
  rw [Trace75BFSLocalWord.field_cast f hf]
  change ((f (direct[j.val]?.getD (0,0,0,0))):V) = _
  rw [←Array.getD_eq_getD_getElem?,DirectBFSRowTransfer.direct_row]

theorem original_back_cast (f : CompactLocalWord.Quad → ℕ) (hf : f (0,0,0,0)=0) (j : Fin 943) :
    CompactLocalWord.field f (back (j.val:V))=(f (Compact943Data.row (rowBackward j)):V) := by
  rw [back_cast,CompactLocalWord.field_cast f hf]
  change ((f (original[(rowBackward j).val]?.getD (0,0,0,0))):V) = _
  rw [←Array.getD_eq_getD_getElem?,DirectBFSRowTransfer.original_row]

theorem transfer (b : V → V) (N s : V) (hw : Trace75BFSLocalWord.Word b N s) :
    CompactLocalWord.Word (fun j => back (b j)) N s := by
  refine ⟨hw.pos,?_,?_,?_,?_,?_⟩
  · intro j hj; exact back_bound _ (hw.tile_lt j hj)
  · intro j hj; exact back_ne_one _ (hw.tile_lt j hj) (hw.tile_ne j hj)
  · rw [hw.marker,back_zero]
  · intro j hj k hk he
    obtain ⟨a,ha,hea⟩ := bounded_standard 943 (b j) (hw.tile_lt j hj)
    obtain ⟨c,hc,hec⟩ := bounded_standard 943 (b k) (hw.tile_lt k hk)
    let i : Fin 943 := ⟨a,ha⟩
    let l : Fin 943 := ⟨c,hc⟩
    have hed := hw.east j hj k hk he
    rw [hea,hec,direct_cast _ rfl i,direct_cast _ rfl l] at hed
    have hnat : (DirectBFSSymbolicKernel.row i).2.2.1=(DirectBFSSymbolicKernel.row l).1 := by exact_mod_cast hed
    rw [hea,hec,original_back_cast _ rfl i,original_back_cast _ rfl l]
    exact_mod_cast DirectBFSEdgeReflection.horizontal i l hnat
  · intro j hj k hk he
    obtain ⟨a,ha,hea⟩ := bounded_standard 943 (b j) (hw.tile_lt j hj)
    obtain ⟨c,hc,hec⟩ := bounded_standard 943 (b k) (hw.tile_lt k hk)
    let i : Fin 943 := ⟨a,ha⟩
    let l : Fin 943 := ⟨c,hc⟩
    have hed := hw.south j hj k hk he
    rw [hea,hec,direct_cast _ rfl i,direct_cast _ rfl l] at hed
    have hnat : (DirectBFSSymbolicKernel.row i).2.2.2=(DirectBFSSymbolicKernel.row l).2.1 := by exact_mod_cast hed
    rw [hea,hec,original_back_cast _ rfl i,original_back_cast _ rfl l]
    exact_mod_cast DirectBFSEdgeReflection.vertical i l hnat
#print axioms Trace75BFSModelWordTransfer.back_ne_one
#print axioms Trace75BFSModelWordTransfer.direct_cast
#print axioms Trace75BFSModelWordTransfer.original_back_cast
#print axioms Trace75BFSModelWordTransfer.transfer
end Trace75BFSModelWordTransfer
