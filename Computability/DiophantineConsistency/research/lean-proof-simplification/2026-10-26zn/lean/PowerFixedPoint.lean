import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

namespace ProofSimplification.PowerFixedPoint

/-- A fixed point of one power map stays fixed under all iterates of that map. -/
theorem pow_pow_fixed {M : Type*} [Monoid M] (x : M) (a n : ℕ) (h : x ^ a = x) :
    x ^ (a ^ n) = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

/-- Natural bases may remain opaque while their small residue is used to verify the seed. -/
theorem natCast_pow_pow_fixed {m : ℕ} (b a n r : ℕ)
    (hb : (b : ZMod m) = r) (hr : (r : ZMod m) ^ a = r) :
    ((b ^ (a ^ n) : ℕ) : ZMod m) = b := by
  rw [Nat.cast_pow]
  apply pow_pow_fixed
  simpa only [hb] using hr

theorem fixed_47 : (37 : ZMod 47) ^ 120199 = 37 := by reduce_mod_char
theorem fixed_2011 : (1283 : ZMod 2011) ^ 120199 = 1283 := by reduce_mod_char
theorem fixed_auxiliary : (37435 : ZMod 120199) ^ 120199 = 37435 := by reduce_mod_char

-- Exact source statements with a symbolic B; only already-checked source residues assumed.
theorem power_dimension_47 (B : ℕ) (hB : (B : ZMod 47) = 37) (n : ℕ) :
    ((B ^ (120199 ^ n) : ℕ) : ZMod 47) = B :=
  natCast_pow_pow_fixed B 120199 n 37 hB fixed_47

theorem power_dimension_2011 (B : ℕ) (hB : (B : ZMod 2011) = 1283) (n : ℕ) :
    ((B ^ (120199 ^ n) : ℕ) : ZMod 2011) = B :=
  natCast_pow_pow_fixed B 120199 n 1283 hB fixed_2011

theorem power_dimension_auxiliary (B : ℕ) (hB : (B : ZMod 120199) = 37435) (n : ℕ) :
    ((B ^ (120199 ^ n) : ℕ) : ZMod 120199) = B :=
  natCast_pow_pow_fixed B 120199 n 37435 hB fixed_auxiliary

-- Both endpoint tests matter: n=0 is allowed and a=0 forces x=1.
example (B : ℕ) : ((B ^ (120199 ^ 0) : ℕ) : ZMod 47) = B := by simp
example {M : Type*} [Monoid M] (x : M) (hx : x^0=x) : x^(0^3)=x :=
  pow_pow_fixed x 0 3 hx

#print axioms pow_pow_fixed
#print axioms power_dimension_47
#print axioms power_dimension_2011
#print axioms power_dimension_auxiliary
end ProofSimplification.PowerFixedPoint
