import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

namespace NewControllerFixedPower

/-- Iterating a power operation needs a fixed point, not a least order. -/
theorem pow_power_fixed {M : Type*} [Monoid M] {x : M} {p : ℕ}
    (h : x ^ p = x) (n : ℕ) : x ^ (p ^ n) = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

/-- The two fixed controller residues at the checked auxiliary exponent. -/
theorem fixed47 : (37 : ZMod 47) ^ 120199 = 37 := by reduce_mod_char
theorem fixed2011 : (1283 : ZMod 2011) ^ 120199 = 1283 := by reduce_mod_char

theorem fixed47_iterated (n : ℕ) :
    (37 : ZMod 47) ^ (120199 ^ n) = 37 := pow_power_fixed fixed47 n

theorem fixed2011_iterated (n : ℕ) :
    (1283 : ZMod 2011) ^ (120199 ^ n) = 1283 := pow_power_fixed fixed2011 n

/-- The generator clients likewise need just these annihilation facts. -/
theorem generator47 : (37 : ZMod 47) ^ (120199 - 1) = 1 := by reduce_mod_char
theorem generator2011 : (1283 : ZMod 2011) ^ (120199 - 1) = 1 := by reduce_mod_char

/-- The full actual natural base is transported only through its residue. -/
theorem actual_base47 (B : ℕ) (hB : (B : ZMod 47) = 37) (n : ℕ) :
    ((B ^ (120199 ^ n) : ℕ) : ZMod 47) = (B : ZMod 47) := by
  simpa only [Nat.cast_pow, hB] using fixed47_iterated n

theorem actual_base2011 (B : ℕ) (hB : (B : ZMod 2011) = 1283) (n : ℕ) :
    ((B ^ (120199 ^ n) : ℕ) : ZMod 2011) = (B : ZMod 2011) := by
  simpa only [Nat.cast_pow, hB] using fixed2011_iterated n

/-- The zero exponent of the dimension is included. -/
example : (37 : ZMod 47) ^ (120199 ^ 0) = 37 := fixed47_iterated 0

#print axioms pow_power_fixed
#print axioms fixed47_iterated
#print axioms fixed2011_iterated
#print axioms generator47
#print axioms generator2011
end NewControllerFixedPower
