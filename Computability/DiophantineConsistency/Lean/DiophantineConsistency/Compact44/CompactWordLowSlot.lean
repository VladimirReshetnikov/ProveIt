import DiophantineConsistency.Compact44.CompactWordPulseEquality
import DiophantineConsistency.Compact44.CompactPulsePackedCell
import DiophantineConsistency.Compact44.CompactBaseLowNoCarry
import DiophantineConsistency.Compact44.CompactConstructedCarryInput
import DiophantineConsistency.Compact44.CompactSymbolicMaskData

/-! Local low-mask safety transfers to every slot of the packed word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordLowSlot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPackingBlocks
open CompactMarkedTransport CompactSymbolicPorts CompactConstructedWord CompactUniformPackedCell
open CompactWordPulseEquality CompactPulsePackedCell CompactBaseLowNoCarry CompactConstructedCarryInput
attribute [local irreducible] lowNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every valid base or pulsed cell is disjoint from the symbolic low mask. -/
theorem cell_low {row dummy : V → V} {N s j : V}
    (hw : CompactWord row N s) (hj : j < N) (hbool : dummy j ≤ 1) :
    NoCarry (cellWord row dummy j) (lowNat : V) := by
  have hbase := base_noCarry (row j) (hw.tile_ne j hj)
  have hpulse := packedCell_pulse_noCarry (row j) hbase
  rw [CompactSymbolicMaskData.low_eq, cellWord_boolean_pulse row dummy j hbool]
  rcases le_one_iff_eq_zero_or_one.mp hbool with hz | ho
  · simpa only [hz, mul_zero, add_zero] using hbase
  · simpa only [ho, mul_one] using hpulse

/-- Slotwise no-carry for the actual packed word. No high-mask or complete
PackingInput premise is used; this even includes global slot zero. -/
theorem word_low_slots (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hbool : ∀ j, dummy j ≤ 1) :
    ∀ k < 8807*N, NoCarry (dig 67 (packedWord row dummy N) k) (dig 67 (lowNat : V) (k%8807)) := by
  let X : V → V := cellWord row dummy
  letI : 𝚺₁-Function₁ X := word_definable row dummy
  have hX : ∀ j < N, X j < Exp.exp (67*8807) := fun j _ => word_cell_lt row dummy j
  intro k hk
  have hj : k/8807 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807 < 8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807 = k := div_add_mod k 8807
  have hd : dig 67 (packedWord row dummy N) k = dig 67 (X (k/8807)) (k%8807) := by
    calc
      dig 67 (packedWord row dummy N) k =
          dig 67 (packedWord row dummy N) (8807*(k/8807)+k%8807) := by rw [he]
      _ = dig 67 (X (k/8807)) (k%8807) := packed_digit X N _ _ hX hj hp
  rw [hd]
  exact noCarry_dig 67 (X (k/8807)) (lowNat : V) (k%8807)
    (cell_low hw hj (hbool (k/8807)))

#print axioms CompactWordLowSlot.cell_low
#print axioms CompactWordLowSlot.word_low_slots
end CompactWordLowSlot
