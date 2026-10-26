import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
Dependency-light arithmetic interfaces suggested by the current and legacy
DiophantineConsistency proofs. This file deliberately does not import any
project theorem: the generalized lemmas can sit below the current modules.
-/

namespace DiophantineConsistency.ArithmeticRefactors

/- Both CurrentClause2011 and CurrentReflectedGeometry2011 prove the two
   following identities separately at L = 2011. -/
theorem addition_residue {N L : ℕ} [NeZero (N * L)]
    (b : ZMod (N * L)) (e : ℕ) :
    (b + (e : ZMod (N * L))).val % L = (b.val + e) % L := by
  have hh : (((b + (e : ZMod (N * L))).val : ℕ) : ZMod (N * L)) =
      ((b.val + e : ℕ) : ZMod (N * L)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

theorem subtraction_residue {N L : ℕ} [NeZero (N * L)]
    (k : ZMod (N * L)) (e : ℕ) :
    ((k - (e : ZMod (N * L))).val + e) % L = k.val % L := by
  have hh : (((k - (e : ZMod (N * L))).val + e : ℕ) : ZMod (N * L)) =
      (k.val : ZMod (N * L)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

/- A scaled half-radix digit has this exact form, regardless of any digit
   bound. The two original four-valued proofs become corollaries. -/
theorem scaled_div_mod (s x y : ℕ) (hs : 0 < s) :
    s * x % (2 * s) + s * y / (2 * s) = s * (x % 2) + y / 2 := by
  rw [mul_comm 2 s, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ hs]

theorem scaled_half_bound (s x y : ℕ) (hs : 0 < s) (hy : y ≤ 3) :
    s * x % (2 * s) + s * y / (2 * s) ≤ s + 1 := by
  rw [scaled_div_mod s x y hs]
  have hx : x % 2 ≤ 1 := by omega
  have hy' : y / 2 ≤ 1 := by omega
  have hm := Nat.mul_le_mul_left s hx
  omega

theorem scaled_half_parity (s x y : ℕ) (hs : 0 < s)
    (heven : s % 2 = 0) (hy : y ≤ 3) :
    (s * x % (2 * s) + s * y / (2 * s)) % 2 = y / 2 := by
  rw [scaled_div_mod s x y hs, Nat.add_mod, Nat.mul_mod, heven]
  have hy' : y / 2 < 2 := by omega
  simp [Nat.mod_eq_of_lt hy']

#print axioms addition_residue
#print axioms subtraction_residue
#print axioms scaled_div_mod
#print axioms scaled_half_bound
#print axioms scaled_half_parity

end DiophantineConsistency.ArithmeticRefactors
