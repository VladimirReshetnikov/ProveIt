import DirectBFSHaltChosenRank
import DirectBFSModelResidue
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSHaltRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPacking ArithmeticPackingBlocks
open DirectBFSConstructedWord DirectBFSFourFieldsPacking DirectBFSHaltCanonicalPacking
open CompactCanonicalPerturbation CompactRankVariation
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_rank (T c : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<length T ∧ j+stride T<length T) ∧
      PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V)
        (length T) (stride T) (cellWord (row T) δ) ∧
      windowRank (kernel:V) (length T) (stride T) c (cellWord (row T) δ) % (590069*length T) =
        (590069*stride T) % (590069*length T) := by
  apply DirectBFSHaltChosenRank.halt_chosen_rank T c hT
  unfold DirectBFSFourFieldsPacking.kernel
  exact DirectBFSModelResidue.residue
#print axioms DirectBFSHaltRank.halt_rank
end DirectBFSHaltRank
