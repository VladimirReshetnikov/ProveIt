import DirectBFSHighOnlyPacking
import DirectBFSHighPadding
import DirectBFSPhaseZeroHigh
import CompactHighPhaseReduction
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSActivePhasePacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking ArithmeticBinaryCarry ArithmeticWindowDigits
open DirectBFSConstructedWord DirectBFSFourFieldsPacking CompactHighPhaseReduction
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def remaining (p : V) : Prop := (1013≤p ∧ p<1023) ∨ (1065≤p ∧ p<1074) ∨
  p=2195 ∨ p=3296 ∨ p=4393 ∨ p=5495

theorem pack_from_active {row dummy : V → V} {N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (h0 : dummy 0%2=0)
    (hN : 1<N) (hs : 0<s) (hsN : s<N)
    (hMC : (CompactConcreteIncrement.mask:V)+1<Exp.exp 590069)
    (hHPpos : 1≤(CompactSymbolicPorts.highNat:V)) (hHPlt : (CompactSymbolicPorts.highNat:V)<Exp.exp 590069)
    (hactive : ∀ j<N, ∀ p<8792, remaining p →
      NoCarry (dig 67 (blk 590069 (kernel:V) N s (cellWord row dummy) j) p) (dig 67 (CompactSymbolicPorts.highNat:V) p)) :
    PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V) N s (cellWord row dummy) := by
  have hsmall : ∀ j<N, cellWord row dummy j<Exp.exp (67*3297+1:V) := by
    intro j hj
    have hd : dummy j%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
    have h := DirectBFSCellSizeBound.packedCell_lt_support (row j) (dummy j%2) (hw.tile_ne j hj) hd
    exact lt_of_lt_of_le h (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hsum := DirectBFSKernelBlockSize.cell_sum_of_small hw.pos hsmall (s:=s)
  have hall : ∀ j<N, NoCarry (blk 590069 (kernel:V) N s (cellWord row dummy) j) (CompactSymbolicPorts.highNat:V) := by
    intro j hj
    apply CompactHighPhaseReduction.noCarry_of_active
    · have hb : blk 590069 (kernel:V) N s (cellWord row dummy) j < Exp.exp (590069:V) := by
        exact lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le (cellWord row dummy j))) (hsum j hj)
      simpa only [show (67*8807:V)=590069 by norm_num] using hb
    · intro p _ hp
      exact DirectBFSHighPadding.word_padding row dummy hw j hj p hp
    · intro p hp ha
      rcases ha with hz | hr
      · rw [hz]
        exact DirectBFSPhaseZeroHigh.phase_zero_noCarry hw
      · exact hactive j hj p hp hr
  exact DirectBFSHighOnlyPacking.pack_from_all_high hw h0 hN hs hsN hMC hHPpos hHPlt hall
#print axioms DirectBFSActivePhasePacking.pack_from_active
end DirectBFSActivePhasePacking
