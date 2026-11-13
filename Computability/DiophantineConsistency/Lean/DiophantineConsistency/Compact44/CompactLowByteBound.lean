import DiophantineConsistency.Compact44.CompactLowByteWindow

/-! A non-normalizing upper bound for the MC byte reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteBound
open CompactLowByteWindow

theorem low_lt_radix_power : CompactSymbolicPorts.lowNat < (2^67)^8807 := by
  have h : Nat.ofDigits (2^67) lowDigits < (2^67)^lowDigits.length :=
    Nat.ofDigits_lt_base_pow_length (by norm_num) lowDigits_bounded
  rw [lowDigits_length] at h
  exact h

theorem radix_power_lt_byte_power : (2:ℕ)^(67*8807) < 256^73759 := by
  rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  apply Nat.pow_lt_pow_right (a := 2)
  · omega
  · omega

theorem low_lt_byte_power : CompactSymbolicPorts.lowNat < 256^73759 := by
  have h := low_lt_radix_power
  rw [← pow_mul] at h
  exact h.trans radix_power_lt_byte_power

#print axioms CompactLowByteBound.low_lt_radix_power
#print axioms CompactLowByteBound.radix_power_lt_byte_power
#print axioms CompactLowByteBound.low_lt_byte_power
end CompactLowByteBound
