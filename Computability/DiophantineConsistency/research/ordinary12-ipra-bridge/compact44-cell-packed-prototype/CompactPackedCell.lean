import CompactCellDigitDef
import DiophantineConsistency.ArithmeticPackingBlocks

/-! A represented local cell, for fixed model row and dummy parameters.
This is not yet a uniformly definable cell word or a packing certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPackedCell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactSymbolicKernel CompactForwardCellInputs CompactWordCellClient
open CompactCellDigit CompactCellDigitDef

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Each subdigit is in radix 2^67; the cell has exactly 8807 subdigits. -/
def packedCell (a d : V) : V := bsum 67 (cellDigit a d) 8807

theorem digit_bound (a d : V) (hd : d ≤ 1) (k : V) :
    cellDigit a d k < Exp.exp (67 : V) := by
  have h2 : (2 : V) ≤ Exp.exp 67 := by
    simpa using exp_monotone_le.mpr (show (1 : V) ≤ 67 by norm_num)
  exact lt_of_le_of_lt (cellDigit_le_one a d k hd) (lt_of_lt_of_le one_lt_two h2)

theorem packedCell_lt (a d : V) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (67 * 8807 : V) := by
  letI : 𝚺₁-Function₁ (cellDigit a d) := cellDigit_definable a d
  exact bsum_lt (fun k _ => digit_bound a d hd k)

theorem packedCell_digit (a d k : V) (hd : d ≤ 1) (hk : k < 8807) :
    dig 67 (packedCell a d) k = cellDigit a d k := by
  letI : 𝚺₁-Function₁ (cellDigit a d) := cellDigit_definable a d
  exact dig_bsum (fun j _ => digit_bound a d hd j) hk

theorem packedCell_selector (a d : V) (hd : d ≤ 1) (i : Fin 943) :
    dig 67 (packedCell a d) (i.val : V) = selector a i := by
  rw [packedCell_digit a d _ hd (by exact_mod_cast (show i.val < 8807 by have := i.isLt; omega))]
  exact selector_digit a d i

theorem packedCell_copy (a d : V) (hd : d ≤ 1) (i : Fin 41) :
    dig 67 (packedCell a d) (position i : V) = payloadBit (payload a) i := by
  rw [packedCell_digit a d _ hd (by exact_mod_cast (show position i < 8807 by have := position_lt_target i; omega))]
  exact copy_digit a d i

theorem packedCell_dummy (a d : V) (hd : d ≤ 1) :
    dig 67 (packedCell a d) 1063 = d := by
  rw [packedCell_digit a d _ hd (by norm_num)]
  exact dummy_digit a d

/-- A row numbered zero sets the least significant bit of its cell. -/
theorem packedCell_origin (d : V) (hd : d ≤ 1) : 1 ≤ packedCell 0 d := by
  have h := packedCell_selector (0 : V) d hd ⟨0, by decide⟩
  have hzero : dig 67 (packedCell (0 : V) d) 0 = 1 := by
    simpa [selector] using h
  rw [dig_zero_index] at hzero
  rw [← hzero]
  exact mod_le _ _

#print axioms CompactPackedCell.packedCell_lt
#print axioms CompactPackedCell.packedCell_digit
#print axioms CompactPackedCell.packedCell_selector
#print axioms CompactPackedCell.packedCell_copy
#print axioms CompactPackedCell.packedCell_dummy
#print axioms CompactPackedCell.packedCell_origin
end CompactPackedCell
