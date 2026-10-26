import Std.Tactic

/-!
Generic arithmetic behind `NativeCyclicRotation.shiftDigits` at half a radix.
This standalone module uses Lean 4.32.0 core/Std only. It changes neither the
cyclic predecessor nor any definition in the source repository.
-/

namespace DiophantineConsistency.ProofReview

theorem half_shift_formula {s : Nat} (hs : 0 < s) (a b : Nat) :
    (s * a) % (2 * s) + (s * b) / (2 * s) = s * (a % 2) + b / 2 := by
  rw [Nat.mul_comm 2 s, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ hs]

/-- Only the predecessor digit needs a bound; the current digit is arbitrary. -/
theorem half_shift_bound {s a b : Nat} (hs : 0 < s) (hb : b ≤ 3) :
    (s * a) % (2 * s) + (s * b) / (2 * s) ≤ s + 1 := by
  rw [half_shift_formula hs]
  have ha : a % 2 ≤ 1 := by omega
  have hm := Nat.mul_le_mul_left s ha
  omega

/-- Even scale kills the low contribution modulo two. -/
theorem half_shift_parity {s a b : Nat} (hs : 0 < s)
    (heven : s % 2 = 0) (hb : b ≤ 3) :
    ((s * a) % (2 * s) + (s * b) / (2 * s)) % 2 = b / 2 := by
  rw [half_shift_formula hs]
  simp only [Nat.add_mod, Nat.mul_mod, heven, Nat.zero_mul, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (show b / 2 < 2 by omega)

#print axioms half_shift_formula
#print axioms half_shift_bound
#print axioms half_shift_parity

end DiophantineConsistency.ProofReview
