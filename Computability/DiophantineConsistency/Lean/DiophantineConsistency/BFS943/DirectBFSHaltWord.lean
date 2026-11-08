import DiophantineConsistency.BFS943.DirectBFSModelForwardWord
import DiophantineConsistency.Compact44.OldWordIdentification
import DiophantineConsistency.Compact44.CompactHaltDimensions
import DiophantineConsistency.ArithmeticPackingBlocks
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSHaltWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPackingBlocks ArithmeticPow
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_to_local {b : V → V} {N s : V} (h : CompactMarkedTransport.CompactWord b N s) :
    CompactLocalWord.Word b N s := by
  refine ⟨h.pos,h.tile_lt,h.tile_ne,h.marker,?_,?_⟩
  · intro j hj k hk he
    rw [OldWordIdentificationDraft.field_eq,OldWordIdentificationDraft.field_eq]
    exact h.east j hj k hk he
  · intro j hj k hk he
    rw [OldWordIdentificationDraft.field_eq,OldWordIdentificationDraft.field_eq]
    exact h.south j hj k hk he

theorem halt_direct_word (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ (b : V → V) (N W s : V), (𝚺₁-Function₁ b) ∧
      N=power 581197 (T+1)*power 581197 (T+3) ∧ s=power 581197 (T+1) ∧
      Blocks 10 b N W ∧ DirectBFSLocalWord.Word b N s := by
  obtain ⟨hd,hw⟩ := CompactHaltDimensions.halt_compact_word_powers T hT
  let b : V → V := fun j => CompactTableLookup.rowLookup
    (ArithmeticTilingBand.word T (power 581197 (T+1)) (power 581197 (T+3)) j)
  let N : V := power 581197 (T+1)*power 581197 (T+3)
  let s : V := power 581197 (T+1)
  letI : 𝚺₁-Function₁[V] b := hd
  have hl : CompactLocalWord.Word b N s := old_to_local hw
  let b' : V → V := fun j => DirectBFSModelForwardMap.forward (b j)
  have hd' : 𝚺₁-Function₁[V] b' := by dsimp [b']; definability
  obtain ⟨W,hW⟩ := DirectBFSModelForwardMap.represented b N hl.tile_lt
  exact ⟨b',N,W,s,hd',rfl,rfl,hW,DirectBFSModelForwardWord.transfer b N s hl⟩
#print axioms DirectBFSHaltWord.old_to_local
#print axioms DirectBFSHaltWord.halt_direct_word
end DirectBFSHaltWord
