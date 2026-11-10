import DiophantineConsistency.BFS943.DirectBFSWordPacking
import DiophantineConsistency.BFS943.DirectBFSHaltWord
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSHaltCanonicalPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking ArithmeticPow
open DirectBFSConstructedWord DirectBFSFourFieldsPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def length (T : V) : V := power 581197 (T+1)*power 581197 (T+3)
def stride (T : V) : V := power 581197 (T+1)
def row (T j : V) : V := DirectBFSModelForwardMap.forward (CompactTableLookup.rowLookup
    (ArithmeticTilingBand.word T (power 581197 (T+1)) (power 581197 (T+3)) j))

theorem halt_pack (T : V) (dummy : V → V) [𝚺₁-Function₁ dummy]
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0)
    (h0 : dummy 0%2=0)
    (hMC : (CompactConcreteIncrement.mask:V)+1<Exp.exp 590069)
    (hHPpos : 1≤(CompactSymbolicPorts.highNat:V)) (hHPlt : (CompactSymbolicPorts.highNat:V)<Exp.exp 590069) :
    (𝚺₁-Function₁ (row T)) ∧ DirectBFSLocalWord.Word (row T) (length T) (stride T) ∧
    1<length T ∧ 0<stride T ∧ stride T<length T ∧
    PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V)
      (length T) (stride T) (cellWord (row T) dummy) := by
  obtain ⟨hd,hw⟩ := CompactHaltDimensions.halt_compact_word_powers T hT
  let b : V → V := fun j => CompactTableLookup.rowLookup
    (ArithmeticTilingBand.word T (power 581197 (T+1)) (power 581197 (T+3)) j)
  letI : 𝚺₁-Function₁[V] b := hd
  have hd' : 𝚺₁-Function₁[V] (row T) := by unfold row; definability
  letI : 𝚺₁-Function₁[V] (row T) := hd'
  have hl : CompactLocalWord.Word b (length T) (stride T) := DirectBFSHaltWord.old_to_local hw
  have hdword : DirectBFSLocalWord.Word (row T) (length T) (stride T) :=
    DirectBFSModelForwardWord.transfer b (length T) (stride T) hl
  obtain ⟨hA,_,hB,_⟩ := CompactHaltDimensions.dimensions T
  have h5 : (5:V) ≤ stride T := by
    apply le_trans _ hA
    exact le_add_of_nonneg_left (Arithmetic.zero_le (2*T))
  have hstride : 0 < stride T := lt_of_lt_of_le (by norm_num) h5
  have hB' : (1:V) < power 581197 (T+3) := lt_of_lt_of_le (by norm_num) hB
  have hlt : stride T < length T := by
    change stride T < stride T * power 581197 (T+3)
    calc
      _ = stride T * 1 := (mul_one _).symm
      _ < _ := mul_lt_mul_of_pos_left hB' hstride
  have hlen : 1 < length T := lt_of_le_of_lt (pos_iff_one_le.mp hstride) hlt
  exact ⟨hd',hdword,hlen,hstride,hlt,DirectBFSWordPacking.pack_word hdword h0 hlen hstride hlt hMC hHPpos hHPlt⟩
#print axioms DirectBFSHaltCanonicalPacking.halt_pack
end DirectBFSHaltCanonicalPacking
