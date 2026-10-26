import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-! A proof experiment for ProveIt commit 9f35798db4a63c25e435fca14d75931144657d7e.
This standalone file does not import or modify the production development. -/
namespace ProofSimplification.ResidueTower

/-- A fixed point of one powering map is fixed by all its iterates. No prime,
finite-field, invertibility, or exact-order hypothesis is needed. -/
theorem pow_power_fixed {M : Type*} [Monoid M] (x : M) (p : ℕ)
    (h : x ^ p = x) (n : ℕ) : x ^ (p ^ n) = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

/-- Coprimality only sees the underlying prime support. The one-sided form
keeps the n=0 boundary without falsely requiring its converse. -/
theorem coprime_power_modulus {a b d p : ℕ}
    (h : a ≡ b [MOD d * p]) (hb : Nat.Coprime b (d * p)) (n : ℕ) :
    Nat.Coprime a (d * p ^ n) := by
  have ha : Nat.Coprime a (d * p) := by
    rw [Nat.coprime_iff_gcd_eq_one, h.gcd_eq]
    exact hb
  obtain ⟨hd, hp⟩ := Nat.coprime_mul_iff_right.mp ha
  exact hd.mul_right (hp.pow_right n)

def gamma (r B K p rw n : ℕ) : ℕ :=
  r * ((B ^ (p ^ n)) ^ 2 - 1) *
    (1 + B ^ (p ^ n) * (K + B ^ (p ^ rw)))

def gammaSeed (r B K : ℕ) : ℕ :=
  r * (B ^ 2 - 1) * (1 + B * K + B ^ 2)

/-- All parameter dependence vanishes in a single residue ring. The natural
subtraction is justified before translating it into ring subtraction. -/
theorem gamma_cast_seed (r B K p d rw n : ℕ) (hB : 1 ≤ B)
    (hfixed : (B : ZMod (d * p)) ^ p = B) :
    (gamma r B K p rw n : ZMod (d * p)) = gammaSeed r B K := by
  have hq : 1 ≤ (B ^ (p ^ n)) ^ 2 := one_le_pow₀ (one_le_pow₀ hB)
  have hs : 1 ≤ B ^ 2 := one_le_pow₀ hB
  simp only [gamma, gammaSeed, Nat.cast_mul, Nat.cast_add,
    Nat.cast_sub hq, Nat.cast_sub hs, Nat.cast_pow, Nat.cast_one]
  rw [pow_power_fixed (B : ZMod (d * p)) p hfixed n,
    pow_power_fixed (B : ZMod (d * p)) p hfixed rw]
  ring

/-- One fixed unit certificate proves the whole two-parameter family. -/
theorem gamma_coprime (r B K p d : ℕ) (hB : 1 ≤ B)
    (hfixed : (B : ZMod (d * p)) ^ p = B)
    (hseed : Nat.Coprime (gammaSeed r B K) (d * p)) (rw n : ℕ) :
    Nat.Coprime (gamma r B K p rw n) (d * p ^ n) := by
  apply coprime_power_modulus (b := gammaSeed r B K) _ hseed n
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    (gamma_cast_seed r B K p d rw n hB hfixed)

/-- Actual B=2^94517 and auxiliary=120199: one finite modular calculation
replaces order-based and Frobenius-based parameter transport. -/
theorem controller_fixed_point :
    ((2 : ZMod (94517 * 120199)) ^ 94517) ^ 120199 =
      (2 : ZMod (94517 * 120199)) ^ 94517 := by
  reduce_mod_char

/-- CRT combines already checked literal kernel residues; it does not
replace the maintained kernel by an arbitrary congruent natural. -/
theorem kernel_residue (K : ℕ) (h47 : K % 47 = 26)
    (h2011 : K % 2011 = 1995) (haux : K % 120199 = 114787) :
    K ≡ 1491904576 [MOD 94517 * 120199] := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 94517 120199)).mp
  constructor
  · change K ≡ 1491904576 [MOD 47 * 2011]
    apply (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 47 2011)).mp
    constructor
    · change K % 47 = 1491904576 % 47
      rw [h47]
    · change K % 2011 = 1491904576 % 2011
      rw [h2011]
  · change K % 120199 = 1491904576 % 120199
    rw [haux]

def currentB : ℕ := 2 ^ 94517
def currentR : ℕ := 2 ^ 45919

-- Prevent accidental expansion of giant natural powers in elaboration.
attribute [local irreducible] currentB currentR

theorem currentB_cast : (currentB : ZMod (94517 * 120199)) = 10287028452 := by
  rw [currentB, Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem currentR_cast : (currentR : ZMod (94517 * 120199)) = 9930929229 := by
  rw [currentR, Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

/-- A concrete certificate for the maintained factors. K remains symbolic,
and its three inputs are exactly the residues proved in the repository. -/
theorem current_seed_coprime (K : ℕ) (h47 : K % 47 = 26)
    (h2011 : K % 2011 = 1995) (haux : K % 120199 = 114787) :
    Nat.Coprime (gammaSeed currentR currentB K) (94517 * 120199) := by
  have hK : (K : ZMod (94517 * 120199)) = 1491904576 :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (kernel_residue K h47 h2011 haux)
  have hB : 1 ≤ currentB := by rw [currentB]; exact one_le_pow₀ (by decide)
  have he : (gammaSeed currentR currentB K : ZMod (94517 * 120199)) = 706142772 := by
    simp only [gammaSeed, Nat.cast_mul, Nat.cast_sub (one_le_pow₀ hB : 1 ≤ currentB ^ 2),
      Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [currentB_cast, currentR_cast, hK]
    reduce_mod_char
  have hm : gammaSeed currentR currentB K ≡ 706142772 [MOD 94517 * 120199] :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp he
  rw [Nat.coprime_iff_gcd_eq_one, hm.gcd_eq]
  decide

/-- All exponents, including rw=0 and n=0, share the same certified seed. -/
theorem current_gamma_coprime (K : ℕ) (h47 : K % 47 = 26)
    (h2011 : K % 2011 = 1995) (haux : K % 120199 = 114787) (rw n : ℕ) :
    Nat.Coprime (gamma currentR currentB K 120199 rw n) (94517 * 120199 ^ n) := by
  apply gamma_coprime
  · rw [currentB]
    exact one_le_pow₀ (by decide)
  · simpa only [currentB, Nat.cast_pow, Nat.cast_ofNat] using controller_fixed_point
  · exact current_seed_coprime K h47 h2011 haux

-- The zero exponent is included by the same theorem.
example {M : Type*} [Monoid M] (x : M) (p : ℕ) (h : x ^ p = x) :
    x ^ (p ^ 0) = x := pow_power_fixed x p h 0

-- A uniform converse would be false at n=0.
example : Nat.Coprime 3 (2 * 3 ^ 0) ∧ ¬ Nat.Coprime 3 (2 * 3) := by decide

#print axioms pow_power_fixed
#print axioms coprime_power_modulus
#print axioms gamma_cast_seed
#print axioms gamma_coprime
#print axioms controller_fixed_point
#print axioms kernel_residue
#print axioms current_seed_coprime
#print axioms current_gamma_coprime

end ProofSimplification.ResidueTower
