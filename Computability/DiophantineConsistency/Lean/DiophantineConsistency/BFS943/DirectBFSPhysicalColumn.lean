import DiophantineConsistency.BFS943.DirectBFSHighOnlyPacking
import DiophantineConsistency.BFS943.DirectBFSAlignedZeroCarry
import DiophantineConsistency.Compact44.CompactPartialPackingTransport

/-! Carry-free columns for the physical normalized blocks of a compact word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSPhysicalColumn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks ArithmeticPacking
  CompactHeterogeneousCarry
open CompactSymbolicKernel DirectBFSSymbolicKernel DirectBFSLocalWord
  CompactGenericAlignedMass DirectBFSModelMass CompactTwoBandFlatten
open DirectBFSCellDigit DirectBFSPackedCell DirectBFSUniformPackedCell DirectBFSConstructedWord
  DirectBFSCellProduct DirectBFSKernelBlockSize DirectBFSCellSizeBound
open CompactPartialPackingTransport DirectBFSAlignedZeroCarry DirectBFSStencilZeroCarry
  CompactBitRotation CompactPartialBandRotation
attribute [local irreducible] paramKernel rho selectors copies

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Each physical block digit equals the exact raw stencil column, and the
same column has zero cyclic carry, for every valid cell and local phase. -/
theorem physical_column (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1 < N) (hs : s < N)
    :
    ∀ j < N, ∀ q < 8807,
      let C := packedWord row dummy N
      let W := GenericBandCarryFamily.word (8807*N) C (bandOffsets position)
        (temporalWord (8807*N) (67*(8807*s)) C)
      carry 67 (8807*N) (coeff : Idx → V) W (8807*j+q) = 0 ∧
      dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) q =
        raw 67 coeff W (8807*j+q) := by
  have hhi : ∀ j < N, (paramKernel rho : V) * cellWord row dummy j <
      Exp.exp 590069 * Exp.exp 590069 := by
    intro j hj
    exact normalized_cell_product_lt (row j) (dummy j) (hw.tile_ne j hj)
  have hsmall : ∀ j < N, cellWord row dummy j < Exp.exp (67*3297+1 : V) := by
    intro j hj
    have hd : dummy j%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
    have h := packedCell_lt_support (row j) (dummy j%2) (hw.tile_ne j hj) hd
    exact lt_of_lt_of_le h (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hcell : ∀ j < N, cellWord row dummy j +
      blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j < Exp.exp 590069 :=
    cell_sum_of_small hw.pos hsmall
  have horigin : 1 ≤ cellWord row dummy 0 := by
    change 1 ≤ normalizedCell (row 0) (dummy 0)
    unfold normalizedCell
    rw [hw.marker]
    exact packedCell_origin (dummy 0 % 2) (lt_two_iff_le_one.mp (mod_lt _ (by norm_num)))
  letI : 𝚺₁-Function₁ (cellWord row dummy) := word_definable row dummy
  have ht : TransportInput 590069 (paramKernel rho : V) N s (cellWord row dummy) :=
    ⟨hN, hs, hhi, hcell, horigin⟩
  have hD : (67 : V) * 8807 = 590069 := by norm_num
  have hCeq : Cw 590069 N (cellWord row dummy) = packedWord row dummy N := by
    unfold Cw packedWord
    rw [← hD]
  have hremainder :
      (((((paramKernel rho : ℕ) : V) + Exp.exp (67*(8807*s))) * packedWord row dummy N) %
        (Exp.exp (67*(8807*N))-1)) = Fw 590069 (paramKernel rho : V) N s (cellWord row dummy) := by
    have hr := transport_residue ht
    rw [hCeq] at hr
    simpa only [← mul_assoc, hD] using hr
  intro j hj q hq
  have hk : 8807*j+q < 8807*N := by
    calc
      8807*j+q < 8807*j+8807 := by
        simpa only [add_comm] using add_lt_add_left hq (8807*j)
      _ = 8807*(j+1) := by ring
      _ ≤ 8807*N := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hj) (by norm_num)
  have hc := packed_word_zero_carry row dummy N (8807*s) hw.pos (8807*j+q) hk
  have hd : dig 67 (Fw 590069 (paramKernel rho : V) N s (cellWord row dummy)) (8807*j+q) =
      dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) q := by
    have hb := blk_lt ht
    unfold Fw
    have hsub := DirectBFSConstructedWord.subdigit
      (bsum 590069 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy)) N) j q hq
    rw [hD, dig_bsum hb hj] at hsub
    exact hsub.symm
  rw [hremainder, hd] at hc
  exact hc

#print axioms DirectBFSPhysicalColumn.physical_column
end DirectBFSPhysicalColumn
