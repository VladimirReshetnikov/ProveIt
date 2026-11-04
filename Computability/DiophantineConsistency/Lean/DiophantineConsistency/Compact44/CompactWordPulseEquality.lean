import DiophantineConsistency.Compact44.CompactConstructedWord
import DiophantineConsistency.Compact44.CompactCellPulseEquality

/-! Link the represented outer word to the explicit pulse cell family. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactWordPulseEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticPackingBlocks
open CompactPackedCell CompactUniformPackedCell CompactConstructedWord CompactCellPulseEquality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cellWord_pulse (row dummy : V → V) (j : V) :
    cellWord row dummy j = packedCell (row j) 0 + Exp.exp (67*1063) * (dummy j % 2) :=
  normalized_eq_pulse _ _

theorem cellWord_boolean_pulse (row dummy : V → V) (j : V) (hd : dummy j ≤ 1) :
    cellWord row dummy j = packedCell (row j) 0 + Exp.exp (67*1063) * dummy j := by
  rw [cellWord_pulse, mod_eq_self_of_lt (lt_two_iff_le_one.mpr hd)]

theorem packedWord_pulses (row dummy : V → V) (N : V) :
    packedWord row dummy N =
      bsum (67*8807) (fun j => packedCell (row j) 0 + Exp.exp (67*1063) * (dummy j % 2)) N := by
  unfold packedWord
  congr 1
  funext j
  exact cellWord_pulse row dummy j

#print axioms CompactWordPulseEquality.cellWord_pulse
#print axioms CompactWordPulseEquality.cellWord_boolean_pulse
#print axioms CompactWordPulseEquality.packedWord_pulses
end CompactWordPulseEquality
