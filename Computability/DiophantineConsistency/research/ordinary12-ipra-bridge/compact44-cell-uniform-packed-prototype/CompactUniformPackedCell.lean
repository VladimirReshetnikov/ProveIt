import CompactPackedCell
import UniformBlocks

/-! Uniformly represented cells, normalized at the dummy input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactUniformPackedCell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactCellDigit CompactCellDigitUniform CompactPackedCell UniformBlocks

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Normalization provides a Boolean dummy digit for every parameter value. -/
def normalizedCell (a d : V) : V := packedCell a (d % 2)

theorem normalizedCell_definable : 𝚺₁-Function₂ (normalizedCell : V → V → V) := by
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  haveI : 𝚺₁-Function₃ (fun a d k : V => cellDigit a (d % 2) k) := by definability
  unfold normalizedCell packedCell
  apply bsum_uniform (fun a d k => cellDigit a (d % 2) k) 67 8807
  intro a d k
  exact digit_bound a (d % 2) (lt_two_iff_le_one.mp (mod_lt d (by norm_num))) k

theorem normalizedCell_eq (a d : V) (hd : d ≤ 1) :
    normalizedCell a d = packedCell a d := by
  unfold normalizedCell
  rw [mod_eq_self_of_lt (lt_two_iff_le_one.mpr hd)]

/-- Pointwise bounded rows and dummy bits now yield a definable cell word. -/
theorem word_definable (row dummy : V → V)
    [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] :
    𝚺₁-Function₁ (fun j => normalizedCell (row j) (dummy j)) := by
  letI : 𝚺₁-Function₂ (normalizedCell : V → V → V) := normalizedCell_definable
  definability

theorem word_cell_lt (row dummy : V → V) (j : V) :
    normalizedCell (row j) (dummy j) < Exp.exp (67 * 8807 : V) := by
  exact packedCell_lt (row j) (dummy j % 2)
    (lt_two_iff_le_one.mp (mod_lt (dummy j) (by norm_num)))

#print axioms CompactUniformPackedCell.normalizedCell_definable
#print axioms CompactUniformPackedCell.normalizedCell_eq
#print axioms CompactUniformPackedCell.word_definable
#print axioms CompactUniformPackedCell.word_cell_lt
end CompactUniformPackedCell
