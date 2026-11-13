import RadixShiftedDigits
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactFixedBeta

/-! Symbolic radix digits of the once-shifted MF high-mask port. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactShiftedHighDigits
open CompactHighPopulation
attribute [local irreducible] highDigits CompactFixedBeta.betaNat CompactSymbolicPorts.highNat

theorem high_head : highDigits = 4 :: highDigits.tail := by
  unfold highDigits
  rfl

theorem high_tail_length : highDigits.tail.length + 1 = 8807 := by
  have h := digits_length
  rw [high_head] at h
  simpa only [List.length_cons] using h

def shiftedDigits : List ℕ := (3 :: highDigits.tail) ++ [1]

theorem shifted_digits_length : shiftedDigits.length = 8808 := by
  unfold shiftedDigits
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h := high_tail_length
  omega

theorem shifted_digits_bounded : ∀ x ∈ shiftedDigits, x < 2^67 := by
  intro x hx
  simp only [shiftedDigits, List.mem_append, List.mem_cons, List.mem_singleton] at hx
  rcases hx with (rfl | ht) | rfl
  · norm_num
  · have hh : x ∈ highDigits := by
      rw [high_head]
      exact List.mem_cons_of_mem 4 ht
    exact digit_lt x hh
  · norm_num

theorem shifted_value :
    CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat =
      Nat.ofDigits (2^67) shiftedDigits := by
  have h := RadixShiftedDigits.add_repunit (2^67) 8807 3 highDigits.tail
    (by norm_num) high_tail_length
  have hbeta : CompactFixedBeta.betaNat = (2^67)^8807 - 1 := by
    unfold CompactFixedBeta.betaNat
    rw [← pow_mul]
  rw [hbeta]
  unfold CompactSymbolicPorts.highNat
  rw [high_head]
  exact h

#print axioms CompactShiftedHighDigits.shifted_digits_length
#print axioms CompactShiftedHighDigits.shifted_digits_bounded
#print axioms CompactShiftedHighDigits.shifted_value
end CompactShiftedHighDigits
