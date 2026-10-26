import Std.Tactic

/-!
Scalar interface for an exact natural digit/carry decomposition. These lemmas
support the existing `Facts` interface; they do not assume a zero incoming
carry and do not impose any cyclic starting point.
-/

namespace DiophantineConsistency.ProofReview

theorem quotient_of_decomposition {raw digit carry radix : Nat}
    (hd : digit < radix) (h : raw = digit + radix * carry) :
    carry = raw / radix := by
  rw [h, Nat.add_mul_div_left _ _ (show 0 < radix by omega),
    Nat.div_eq_of_lt hd, Nat.zero_add]

theorem residue_of_decomposition {raw digit carry radix modulus : Nat}
    (hm : modulus ∣ radix) (h : raw = digit + radix * carry) :
    digit % modulus = raw % modulus := by
  rw [h, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hm]
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]

/-- A small raw total resets its outgoing carry. No digit bound is needed. -/
theorem zero_carry_of_decomposition {raw digit carry radix : Nat}
    (hsmall : raw < radix) (h : raw = digit + radix * carry) : carry = 0 := by
  have hd : digit < radix := by omega
  exact (quotient_of_decomposition hd h).trans (Nat.div_eq_of_lt hsmall)

#print axioms quotient_of_decomposition
#print axioms residue_of_decomposition
#print axioms zero_carry_of_decomposition

end DiophantineConsistency.ProofReview
