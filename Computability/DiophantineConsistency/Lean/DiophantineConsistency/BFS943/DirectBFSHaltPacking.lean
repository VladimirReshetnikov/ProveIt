import DiophantineConsistency.BFS943.DirectBFSHaltCanonicalPacking
import DiophantineConsistency.Compact44.CompactSymbolicMaskFields
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSHaltPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking
open DirectBFSConstructedWord DirectBFSFourFieldsPacking DirectBFSHaltCanonicalPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat CompactSymbolicPorts.lowNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_pack (T : V) (dummy : V → V) [𝚺₁-Function₁ dummy]
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) (h0 : dummy 0%2=0) :
    (𝚺₁-Function₁ (row T)) ∧ DirectBFSLocalWord.Word (row T) (length T) (stride T) ∧
    1<length T ∧ 0<stride T ∧ stride T<length T ∧
    PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V)
      (length T) (stride T) (cellWord (row T) dummy) := by
  have hm := CompactSymbolicMaskFields.masks (V:=V)
  rw [CompactSymbolicMaskData.low_eq] at hm
  exact DirectBFSHaltCanonicalPacking.halt_pack T dummy hT h0 hm.1 hm.2.1 hm.2.2
#print axioms DirectBFSHaltPacking.halt_pack
end DirectBFSHaltPacking
