import DirectBFSFourFieldsPacking
import DirectBFSKernelBlockSize
import DirectBFSOriginBlockResidue
import DirectBFSWordBlockPositive
import DirectBFSCellSizeBound
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSHighOnlyPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking ArithmeticBinaryCarry
open DirectBFSConstructedWord DirectBFSFourFieldsPacking
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pack_from_all_high {row dummy : V → V} {N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (h0 : dummy 0%2=0)
    (hN : 1<N) (hs : 0<s) (hsN : s<N)
    (hMC : (CompactConcreteIncrement.mask:V)+1<Exp.exp 590069)
    (hHPpos : 1≤(CompactSymbolicPorts.highNat:V)) (hHPlt : (CompactSymbolicPorts.highNat:V)<Exp.exp 590069)
    (hall : ∀ j<N, NoCarry (blk 590069 (kernel:V) N s (cellWord row dummy) j) (CompactSymbolicPorts.highNat:V)) :
    PackingInput (590069:V) (kernel:V) (CompactConcreteIncrement.mask:V) (CompactSymbolicPorts.highNat:V) N s (cellWord row dummy) := by
  have hsmall : ∀ j<N, cellWord row dummy j<Exp.exp (67*3297+1:V) := by
    intro j hj
    have hd : dummy j%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
    have h := DirectBFSCellSizeBound.packedCell_lt_support (row j) (dummy j%2) (hw.tile_ne j hj) hd
    exact lt_of_lt_of_le h (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hsum := DirectBFSKernelBlockSize.cell_sum_of_small hw.pos hsmall (s:=s)
  have hhigh := DirectBFSOriginBlockResidue.normalized_high_fields hw hs hsN hall
  have hfields : RemainingFields (CompactSymbolicPorts.highNat:V) N s (cellWord row dummy) :=
    ⟨hsum,DirectBFSWordBlockPositive.block_pos hw 0,hhigh.1,hhigh.2⟩
  exact DirectBFSFourFieldsPacking.pack_from_four_fields hw h0 hN hsN hMC hHPpos hHPlt hfields
#print axioms DirectBFSHighOnlyPacking.pack_from_all_high
end DirectBFSHighOnlyPacking
