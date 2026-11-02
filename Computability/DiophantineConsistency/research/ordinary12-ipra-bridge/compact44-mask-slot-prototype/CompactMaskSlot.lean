import DiophantineConsistency.CompactDummyBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactMaskSlot
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinary_at (X M k : V) (h : NoCarry X M)
    (hm : dig 67 M k=Exp.exp 67-2) : dig 67 X k≤1 := by
  have hd := noCarry_dig 67 X M k h
  rw [hm] at hd
  exact CompactDummyBound.ordinary_le_one _ (dig_lt 67 X k) hd

theorem forbidden_at (X M k : V) (h : NoCarry X M)
    (hm : dig 67 M k=Exp.exp 67-1) : dig 67 X k=0 := by
  have hd := noCarry_dig 67 X M k h
  rw [hm] at hd
  exact CompactDummyBound.forbidden_zero _ (dig_lt 67 X k) hd

theorem dummy_at (X M k : V) (h : NoCarry X M)
    (hm : dig 67 M k=Exp.exp 67-4) : dig 67 X k≤3 := by
  have hd := noCarry_dig 67 X M k h
  rw [hm] at hd
  exact CompactDummyBound.dummy_le_three _ (dig_lt 67 X k) hd
end CompactMaskSlot
#print axioms CompactMaskSlot.ordinary_at
#print axioms CompactMaskSlot.forbidden_at
#print axioms CompactMaskSlot.dummy_at
