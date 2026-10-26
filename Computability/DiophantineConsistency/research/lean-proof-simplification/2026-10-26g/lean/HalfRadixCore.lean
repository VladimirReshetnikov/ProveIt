import Mathlib.Tactic

/-!
Reusable arithmetic for the half-radix branch.
Draft written against ProveIt commit 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
Compilation status must be established by the supplied build log.
-/

namespace DiophantineConsistency.RefactorHalfRadix

/-- Splitting at half a radix exposes only the low and high binary bits.
No bound on the present digit `a` is required. -/
theorem half_digit_eq {s : ℕ} (hs : 0 < s) (a b : ℕ) :
    s * a % (2 * s) + s * b / (2 * s) = s * (a % 2) + b / 2 := by
  rw [Nat.mul_comm 2 s, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ hs]

/-- Only the preceding digit needs the two-bit bound. -/
theorem half_digit_le {s : ℕ} (hs : 0 < s) (a b : ℕ) (hb : b ≤ 3) :
    s * a % (2 * s) + s * b / (2 * s) ≤ s + 1 := by
  rw [half_digit_eq hs]
  have ha : a % 2 ≤ 1 := by omega
  have hm : s * (a % 2) ≤ s := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left s ha
  omega

/-- For an even half-radix, parity is exactly the preceding high bit. -/
theorem half_digit_parity {s : ℕ} (hs : 0 < s) (heven : s % 2 = 0)
    (a b : ℕ) (hb : b ≤ 3) :
    (s * a % (2 * s) + s * b / (2 * s)) % 2 = b / 2 := by
  rw [half_digit_eq hs]
  have hdiv : b / 2 < 2 := by omega
  simp only [Nat.add_mod, Nat.mul_mod, heven, Nat.zero_mul, Nat.zero_mod,
    Nat.zero_add, Nat.mod_eq_of_lt hdiv]

#print axioms half_digit_eq
#print axioms half_digit_le
#print axioms half_digit_parity

end DiophantineConsistency.RefactorHalfRadix
