import DiophantineConsistency.Compact44.RadixShiftedDigits
import DiophantineConsistency.Compact44.CompactSymbolicPorts
import DiophantineConsistency.Compact44.CompactFixedBeta

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
  simp only [shiftedDigits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | ht) | rfl
  · norm_num
  · have hh : x ∈ highDigits := by
      rw [high_head]
      exact List.mem_cons_of_mem 4 ht
    exact digit_lt x hh
  · norm_num

theorem shifted_value_generic (b : ℕ) (hb : 0 < b) :
    (b^8807 - 1) + Nat.ofDigits b highDigits = Nat.ofDigits b shiftedDigits := by
  have h := RadixShiftedDigits.add_repunit b 8807 3 highDigits.tail hb high_tail_length
  have hh := congrArg (Nat.ofDigits b) high_head
  calc
    (b^8807 - 1) + Nat.ofDigits b highDigits =
        (b^8807 - 1) + Nat.ofDigits b (4 :: highDigits.tail) := congrArg ((b^8807 - 1) + ·) hh
    _ = Nat.ofDigits b ((3 :: highDigits.tail) ++ [1]) := h
    _ = Nat.ofDigits b shiftedDigits := rfl

theorem shifted_value :
    CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat =
      Nat.ofDigits (2^67) shiftedDigits := by
  have hbeta : CompactFixedBeta.betaNat = (2^67)^8807 - 1 := by
    unfold CompactFixedBeta.betaNat
    rw [← pow_mul]
  have hhigh : CompactSymbolicPorts.highNat = Nat.ofDigits (2^67) highDigits := by
    unfold CompactSymbolicPorts.highNat
    rfl
  calc
    CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat =
        ((2^67)^8807 - 1) + Nat.ofDigits (2^67) highDigits :=
      congrArg₂ (· + ·) hbeta hhigh
    _ = Nat.ofDigits (2^67) shiftedDigits := shifted_value_generic (2^67) (by norm_num)

#print axioms CompactShiftedHighDigits.shifted_digits_length
#print axioms CompactShiftedHighDigits.shifted_digits_bounded
#print axioms CompactShiftedHighDigits.shifted_value
end CompactShiftedHighDigits
