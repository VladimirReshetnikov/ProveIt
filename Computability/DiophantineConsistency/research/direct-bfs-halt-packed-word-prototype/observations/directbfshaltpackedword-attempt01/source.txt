import DirectBFSHaltWord
import DirectBFSConstructedWord
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSHaltPackedWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPow
open CompactSymbolicKernel CompactForwardCellInputs
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_packed_word (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ (b : V → V) (N W s C : V), (𝚺₁-Function₁ b) ∧
      N=power 581197 (T+1)*power 581197 (T+3) ∧ s=power 581197 (T+1) ∧
      Blocks 10 b N W ∧ DirectBFSLocalWord.Word b N s ∧
      1≤C ∧ C<Exp.exp ((67*8807)*N) ∧
      (∀ k<8807*N, dig 67 C k≤1) ∧
      (∀ j<N, ∀ i : Fin 943, dig 67 C (8807*j+(i.val:V))=DirectBFSConstructedWord.wordSelector b i j) ∧
      (∀ j<N, ∀ i : Fin 41, dig 67 C (8807*j+(position i:V))=DirectBFSConstructedWord.wordPayloadBit b i j) := by
  obtain ⟨b,N,W,s,hb,hN,hs,hW,hw⟩ := DirectBFSHaltWord.halt_direct_word T hT
  letI : 𝚺₁-Function₁[V] b := hb
  let dummy : V → V := fun _ => 0
  letI : 𝚺₁-Function₁[V] dummy := by dsimp [dummy]; definability
  refine ⟨b,N,W,s,DirectBFSConstructedWord.packedWord b dummy N,hb,hN,hs,hW,hw,?_,?_,?_,?_,?_⟩
  · exact DirectBFSConstructedWord.marked_word_origin b dummy N s hw
  · exact DirectBFSConstructedWord.packedWord_lt b dummy N
  · exact DirectBFSConstructedWord.word_cap b dummy N
  · exact DirectBFSConstructedWord.word_selector b dummy N
  · exact DirectBFSConstructedWord.word_copy b dummy N
#print axioms DirectBFSHaltPackedWord.halt_packed_word
end DirectBFSHaltPackedWord
