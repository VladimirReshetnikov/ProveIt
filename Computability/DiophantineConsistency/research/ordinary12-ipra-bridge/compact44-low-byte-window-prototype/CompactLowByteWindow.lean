import ByteWindow
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactConcreteMask

/-! Specialize generic little-endian byte windows to the symbolic low mask. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteWindow

def lowDigits : List ℕ :=
  CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support

theorem lowDigits_length : lowDigits.length = 8807 :=
  CompactListMask.digits_length _ _ _ _

theorem lowDigits_bounded : ∀ x ∈ lowDigits, x < 2^67 :=
  CompactListMask.digits_lt _ _ _ _ (by norm_num)

theorem padded_digit (i : ℕ) :
    PaddedRadixDigits.digit lowDigits i =
      if i < 8807 then
        CompactListMask.digit (2^67) 1063 CompactConcreteMask.support i
      else 0 := by
  change lowDigits.getD i 0 = _
  by_cases hi : i < 8807
  · rw [if_pos hi]
    exact CompactListMask.digits_getD _ _ _ _ hi
  · rw [if_neg hi]
    apply List.getD_eq_default
    rw [lowDigits_length]
    omega

theorem low_byte (j : ℕ) :
    (CompactSymbolicPorts.lowNat / 2^(8*j)) % 256 =
      (PaddedRadixDigits.digit lowDigits ((8*j)/67) / 2^((8*j)%67) +
       PaddedRadixDigits.digit lowDigits ((8*j)/67+1) * 2^(67-(8*j)%67)) % 256 := by
  exact ByteWindow.byte lowDigits lowDigits_bounded j

#print axioms CompactLowByteWindow.lowDigits_bounded
#print axioms CompactLowByteWindow.padded_digit
#print axioms CompactLowByteWindow.low_byte
end CompactLowByteWindow
