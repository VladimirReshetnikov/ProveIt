import Mathlib.Tactic

namespace LeanProofs.TwoBaseIntegerExponent

/-!
# Unimodular power collisions

This module formalizes the group-theoretic core of the binomial-gap gcd theorem from
report 23.  If two power collisions have exponent determinant `D`, then both group elements
have `D`-th power one.  Applying this in the unit group of a residue ring gives the local
congruence used in the paper proof.
-/

namespace UnimodularGapCollision

/-- Two power collisions with `p * s = r * q + D` force the `D`-th power of the first
group element to be one. -/
theorem left_pow_eq_one_of_det_forward
    {G : Type*} [CommGroup G] (A B : G) (p q r s D : ℕ)
    (hpq : B ^ q = A ^ p) (hrs : B ^ s = A ^ r)
    (hdet : p * s = r * q + D) :
    A ^ D = 1 := by
  have hpow : A ^ (p * s) = A ^ (r * q) := by
    calc
      A ^ (p * s) = (A ^ p) ^ s := by simp [pow_mul]
      _ = (B ^ q) ^ s := by rw [← hpq]
      _ = B ^ (q * s) := by simp [pow_mul]
      _ = B ^ (s * q) := by rw [Nat.mul_comm q s]
      _ = (B ^ s) ^ q := by simp [pow_mul]
      _ = (A ^ r) ^ q := by rw [hrs]
      _ = A ^ (r * q) := by simp [pow_mul]
  rw [hdet, pow_add] at hpow
  exact mul_left_cancel (show A ^ (r * q) * A ^ D = A ^ (r * q) * 1 by simpa using hpow)

/-- Two power collisions with `p * s = r * q + D` force the `D`-th power of the second
group element to be one. -/
theorem right_pow_eq_one_of_det_forward
    {G : Type*} [CommGroup G] (A B : G) (p q r s D : ℕ)
    (hpq : B ^ q = A ^ p) (hrs : B ^ s = A ^ r)
    (hdet : p * s = r * q + D) :
    B ^ D = 1 := by
  have hdet' : s * p = q * r + D := by
    simpa [Nat.mul_comm] using hdet
  have hpow : B ^ (s * p) = B ^ (q * r) := by
    calc
      B ^ (s * p) = (B ^ s) ^ p := by simp [pow_mul]
      _ = (A ^ r) ^ p := by rw [hrs]
      _ = A ^ (r * p) := by simp [pow_mul]
      _ = A ^ (p * r) := by rw [Nat.mul_comm r p]
      _ = (A ^ p) ^ r := by simp [pow_mul]
      _ = (B ^ q) ^ r := by rw [← hpq]
      _ = B ^ (q * r) := by simp [pow_mul]
  rw [hdet', pow_add] at hpow
  exact mul_left_cancel (show B ^ (q * r) * B ^ D = B ^ (q * r) * 1 by simpa using hpow)

/-- Forward-orientation determinant collision theorem. -/
theorem pow_eq_one_of_det_forward
    {G : Type*} [CommGroup G] (A B : G) (p q r s D : ℕ)
    (hpq : B ^ q = A ^ p) (hrs : B ^ s = A ^ r)
    (hdet : p * s = r * q + D) :
    A ^ D = 1 ∧ B ^ D = 1 :=
  ⟨left_pow_eq_one_of_det_forward A B p q r s D hpq hrs hdet,
    right_pow_eq_one_of_det_forward A B p q r s D hpq hrs hdet⟩

/-- Reverse-orientation determinant collision theorem. -/
theorem pow_eq_one_of_det_reverse
    {G : Type*} [CommGroup G] (A B : G) (p q r s D : ℕ)
    (hpq : B ^ q = A ^ p) (hrs : B ^ s = A ^ r)
    (hdet : r * q = p * s + D) :
    A ^ D = 1 ∧ B ^ D = 1 := by
  exact pow_eq_one_of_det_forward A B r s p q D hrs hpq hdet

/-- In the unimodular forward orientation, both colliding group elements equal one. -/
theorem eq_one_of_det_forward_one
    {G : Type*} [CommGroup G] (A B : G) (p q r s : ℕ)
    (hpq : B ^ q = A ^ p) (hrs : B ^ s = A ^ r)
    (hdet : p * s = r * q + 1) :
    A = 1 ∧ B = 1 := by
  simpa using pow_eq_one_of_det_forward A B p q r s 1 hpq hrs hdet

/-- In the unimodular reverse orientation, both colliding group elements equal one. -/
theorem eq_one_of_det_reverse_one
    {G : Type*} [CommGroup G] (A B : G) (p q r s : ℕ)
    (hpq : B ^ q = A ^ p) (hrs : B ^ s = A ^ r)
    (hdet : r * q = p * s + 1) :
    A = 1 ∧ B = 1 := by
  simpa using pow_eq_one_of_det_reverse A B p q r s 1 hpq hrs hdet

/-! ## Congruence wrappers -/

/-- The forward determinant theorem in the unit group modulo `n`.  This is the exact local
statement used in the binomial-gap gcd argument: two collisions modulo a modulus coprime to
both bases force both `D`-th powers to be one modulo that modulus. -/
theorem modEq_pow_one_of_det_forward
    (n A B p q r s D : ℕ) (hA : A.Coprime n) (hB : B.Coprime n)
    (hpq : B ^ q ≡ A ^ p [MOD n]) (hrs : B ^ s ≡ A ^ r [MOD n])
    (hdet : p * s = r * q + D) :
    A ^ D ≡ 1 [MOD n] ∧ B ^ D ≡ 1 [MOD n] := by
  let Au : (ZMod n)ˣ := ZMod.unitOfCoprime A hA
  let Bu : (ZMod n)ˣ := ZMod.unitOfCoprime B hB
  have hpqU : Bu ^ q = Au ^ p := by
    apply Units.ext
    simpa [Au, Bu, ZMod.coe_unitOfCoprime] using
      (ZMod.natCast_eq_natCast_iff (B ^ q) (A ^ p) n).2 hpq
  have hrsU : Bu ^ s = Au ^ r := by
    apply Units.ext
    simpa [Au, Bu, ZMod.coe_unitOfCoprime] using
      (ZMod.natCast_eq_natCast_iff (B ^ s) (A ^ r) n).2 hrs
  have hcore := pow_eq_one_of_det_forward Au Bu p q r s D hpqU hrsU hdet
  constructor
  · apply (ZMod.natCast_eq_natCast_iff (A ^ D) 1 n).1
    simpa [Au, ZMod.coe_unitOfCoprime] using congrArg Units.val hcore.1
  · apply (ZMod.natCast_eq_natCast_iff (B ^ D) 1 n).1
    simpa [Bu, ZMod.coe_unitOfCoprime] using congrArg Units.val hcore.2

/-- The reverse determinant theorem in the unit group modulo `n`. -/
theorem modEq_pow_one_of_det_reverse
    (n A B p q r s D : ℕ) (hA : A.Coprime n) (hB : B.Coprime n)
    (hpq : B ^ q ≡ A ^ p [MOD n]) (hrs : B ^ s ≡ A ^ r [MOD n])
    (hdet : r * q = p * s + D) :
    A ^ D ≡ 1 [MOD n] ∧ B ^ D ≡ 1 [MOD n] := by
  exact modEq_pow_one_of_det_forward n A B r s p q D hA hB hrs hpq hdet

/-- The forward unimodular case: both bases are congruent to one modulo every common collision
modulus coprime to the bases. -/
theorem modEq_one_of_det_forward_one
    (n A B p q r s : ℕ) (hA : A.Coprime n) (hB : B.Coprime n)
    (hpq : B ^ q ≡ A ^ p [MOD n]) (hrs : B ^ s ≡ A ^ r [MOD n])
    (hdet : p * s = r * q + 1) :
    A ≡ 1 [MOD n] ∧ B ≡ 1 [MOD n] := by
  simpa using modEq_pow_one_of_det_forward n A B p q r s 1 hA hB hpq hrs hdet

/-- The reverse unimodular case. -/
theorem modEq_one_of_det_reverse_one
    (n A B p q r s : ℕ) (hA : A.Coprime n) (hB : B.Coprime n)
    (hpq : B ^ q ≡ A ^ p [MOD n]) (hrs : B ^ s ≡ A ^ r [MOD n])
    (hdet : r * q = p * s + 1) :
    A ≡ 1 [MOD n] ∧ B ≡ 1 [MOD n] := by
  simpa using modEq_pow_one_of_det_reverse n A B p q r s 1 hA hB hpq hrs hdet

end UnimodularGapCollision

end LeanProofs.TwoBaseIntegerExponent
