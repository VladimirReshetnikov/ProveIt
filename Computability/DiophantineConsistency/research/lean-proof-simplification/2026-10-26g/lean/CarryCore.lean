import Mathlib.Data.Nat.Basic

/-! Eliminate a redundant quotient recurrence from normalized-digit records. -/
namespace DiophantineConsistency.RefactorCarry

theorem quotient_of_local {raw digit radix carry : ℕ}
    (hd : digit < radix) (hlocal : raw = digit + radix * carry) :
    carry = raw / radix := by
  rw [hlocal, Nat.add_mul_div_left _ _ (Nat.lt_of_le_of_lt (Nat.zero_le digit) hd),
    Nat.div_eq_of_lt hd, Nat.zero_add]

theorem remainder_of_local {raw digit radix carry : ℕ}
    (hd : digit < radix) (hlocal : raw = digit + radix * carry) :
    digit = raw % radix := by
  rw [hlocal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

#print axioms quotient_of_local
#print axioms remainder_of_local

end DiophantineConsistency.RefactorCarry
