import DiophantineConsistency.Compact44.CompactPulseBitSafety
import DiophantineConsistency.Compact44.CompactUniformPackedCell

/-! Connect the symbolic pulse test to the actual represented compact cell
and to an outer represented word of cells with zero dummy input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPulsePackedCell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticBinaryPopulation ArithmeticWindowDigits ArithmeticPackingBlocks
open CompactPackedCell CompactUniformPackedCell CompactPulseBitSafety
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packedCell_clear_dummy_bit (a : V) :
    fbit (packedCell a 0) (67*1063) = 0 := by
  have h := fbit_dig (67:V) (packedCell a 0) 1063 0 (by norm_num)
  rw [packedCell_dummy a 0 (by simp)] at h
  simpa using h.symm

theorem packedCell_pulse_noCarry (a : V)
    (h : NoCarry (packedCell a 0) CompactConcreteIncrement.mask) :
    NoCarry (packedCell a 0 + Exp.exp (67*1063)) CompactConcreteIncrement.mask :=
  compact_pulse_noCarry (packedCell a 0) h (packedCell_clear_dummy_bit a)

/-- Every selected outer word cell has a clear dummy bit; the row function
is assumed represented and the word length and cell index are model elements. -/
theorem outer_word_clear_dummy_bit (row : V → V) [𝚺₁-Function₁ row]
    (N j : V) (hj : j < N) :
    fbit (bsum (67*8807) (fun t => normalizedCell (row t) 0) N)
      ((67*8807)*j + 67*1063) = 0 := by
  let f : V → V := fun t => normalizedCell (row t) 0
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  letI : 𝚺₁-Function₁ f := word_definable row (fun _ => 0)
  have hf (t : V) (_ : t < N) : f t < Exp.exp (67*8807) := by
    exact word_cell_lt row (fun _ => 0) t
  have hd := dig_bsum hf hj
  have hb := fbit_dig (67*8807 : V) (bsum (67*8807) f N) j (67*1063) (by norm_num)
  rw [hd] at hb
  have hc : f j = packedCell (row j) 0 := normalizedCell_eq (row j) 0 (by simp)
  rw [hc, packedCell_clear_dummy_bit] at hb
  exact hb.symm

#print axioms CompactPulsePackedCell.packedCell_clear_dummy_bit
#print axioms CompactPulsePackedCell.packedCell_pulse_noCarry
#print axioms CompactPulsePackedCell.outer_word_clear_dummy_bit
end CompactPulsePackedCell
