import CompactShiftedHighDigits

/-! An upper bound for 73,759-byte reconstruction of the shifted high port. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactShiftedHighBound
open CompactHighPopulation
attribute [local irreducible] highDigits CompactFixedBeta.betaNat CompactSymbolicPorts.highNat

theorem high_lt_radix_power : CompactSymbolicPorts.highNat < (2^67)^8807 := by
  have h : Nat.ofDigits (2^67) highDigits < (2^67)^highDigits.length :=
    Nat.ofDigits_lt_base_pow_length (by norm_num) digit_lt
  rw [digits_length] at h
  unfold CompactSymbolicPorts.highNat
  exact h

theorem beta_lt_radix_power : CompactFixedBeta.betaNat < (2^67)^8807 := by
  have h : (0:ℕ) < 2^(67*8807) := pow_pos (by decide) _
  unfold CompactFixedBeta.betaNat
  rw [← pow_mul]
  omega

theorem two_radix_lt_byte_power : (2:ℕ)*(2^67)^8807 < 256^73759 := by
  calc
    (2:ℕ)*(2^67)^8807 = 2^(67*8807+1) := by
      conv_rhs => rw [pow_succ, pow_mul]
      exact Nat.mul_comm _ _
    _ < 2^(8*73759) := by
      apply Nat.pow_lt_pow_right (a := 2)
      · omega
      · omega
    _ = 256^73759 := by
      rw [pow_mul, show (2:ℕ)^8 = 256 by norm_num]

theorem shifted_lt_byte_power :
    CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat < 256^73759 := by
  have hb := beta_lt_radix_power
  have hh := high_lt_radix_power
  have hsum : CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat <
      (2:ℕ)*(2^67)^8807 := by omega
  exact hsum.trans two_radix_lt_byte_power

#print axioms CompactShiftedHighBound.shifted_lt_byte_power
end CompactShiftedHighBound
