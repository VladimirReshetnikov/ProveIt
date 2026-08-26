import FabiusFunction.DyadicClosedForm
import FabiusFunction.TwoAdic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Valuation formulas for the Thue--Morse sign

This module completes the two-adic layer of the Thue--Morse formula atlas.
`FabiusFunction.TwoAdic` already proves Legendre's formula for factorials,
Kummer's carry formula for `(a + b).choose a`, and the central-binomial
valuation.  Here we add the remaining exact identities of the atlas's
valuation chapter:

* the successor law `binaryWeight (n + 1) + padicValNat 2 (n + 1)
  = binaryWeight n + 1`: incrementing erases the trailing one-bits and
  writes a single one;
* subadditivity `binaryWeight (a + b) ≤ binaryWeight a + binaryWeight b`,
  which is the qualitative face of carrying;
* the ruler form of the sign: adjacent signs read off the ruler sequence
  `padicValNat 2 (n + 1)`, and the sign itself telescopes into the product
  `∏ (-1) ^ (ν₂(k) + 1)`;
* the Catalan valuation `padicValNat 2 (catalan n) + 1
  = binaryWeight (n + 1)` and its sign form;
* the additive (truncation-free) form of Kummer's theorem and its
  subtraction counterpart: the valuation of `a.choose b` counts the borrows
  of `a - b`, and corrects the Thue--Morse sign of a difference exactly as
  the carry count corrects a sum.

Equations between natural numbers are stated additively (`x + v = y`)
rather than with truncated subtraction, so that every rearrangement is
available to `omega`.  All results are exact and finite; no analysis is
used.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Sign algebra -/

/-- The Thue--Morse sign squares to one. -/
@[simp] theorem thueMorseSign_mul_self (n : ℕ) :
    thueMorseSign n * thueMorseSign n = 1 := by
  rw [thueMorseSign, ← pow_add]
  exact Even.neg_one_pow ⟨binaryWeight n, rfl⟩

/-- Multiplication by a Thue--Morse sign is an involution. -/
theorem thueMorseSign_mul_cancel (n : ℕ) (x : ℤ) :
    thueMorseSign n * (thueMorseSign n * x) = x := by
  rw [← mul_assoc, thueMorseSign_mul_self, one_mul]

/-- Two powers of `-1` agree as soon as their exponents have even sum.  A
small workhorse: the parity identities of this module and its successors are
all proved by exhibiting the even sum to `omega`. -/
theorem neg_one_pow_eq_of_add_even {a b c : ℕ} (h : a + b = 2 * c) :
    ((-1 : ℤ)) ^ a = (-1) ^ b := by
  have hab : ((-1 : ℤ)) ^ a * (-1) ^ b = 1 := by
    rw [← pow_add, h, pow_mul, neg_one_sq, one_pow]
  have hbb : ((-1 : ℤ)) ^ b * (-1) ^ b = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨b, rfl⟩
  calc ((-1 : ℤ)) ^ a
      = (-1) ^ a * ((-1) ^ b * (-1) ^ b) := by rw [hbb, mul_one]
    _ = ((-1) ^ a * (-1) ^ b) * (-1) ^ b := by ring
    _ = (-1) ^ b := by rw [hab, one_mul]

/-! ## The successor law and the ruler sequence -/

/-- **Successor law for the binary weight.**  Incrementing `n` turns the
trailing block of one-bits into zeros and writes a single one just above
it; the number of erased ones is the two-adic valuation of `n + 1`. -/
theorem binaryWeight_succ_add_padicValNat (n : ℕ) :
    binaryWeight (n + 1) + padicValNat 2 (n + 1) = binaryWeight n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- `n = 2k` is even, so `n + 1` is odd and no bit is erased.
        subst hk
        rw [show k + k = 2 * k from (two_mul k).symm,
          binaryWeight_two_mul_add_one, binaryWeight_two_mul,
          padicValNat.eq_zero_of_not_dvd (by omega)]
      · -- `n = 2k + 1` is odd: halving reduces to the induction hypothesis.
        subst hk
        have hval : padicValNat 2 (2 * (k + 1)) =
            1 + padicValNat 2 (k + 1) := by
          rw [padicValNat.mul (p := 2) two_ne_zero (by omega),
            padicValNat.self one_lt_two]
        have hih := ih k (by omega)
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, binaryWeight_two_mul,
          hval, binaryWeight_two_mul_add_one]
        omega

/-- Weakened successor law: incrementing raises the weight by at most one. -/
theorem binaryWeight_succ_le (n : ℕ) :
    binaryWeight (n + 1) ≤ binaryWeight n + 1 := by
  have := binaryWeight_succ_add_padicValNat n
  omega

/-- **Subadditivity of the binary weight.**  Digitwise, an addition can
only merge ones through carries, never create them. -/
theorem binaryWeight_add_le (a : ℕ) :
    ∀ b : ℕ, binaryWeight (a + b) ≤ binaryWeight a + binaryWeight b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro b
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp
      rcases Nat.even_or_odd a with ⟨a', ha⟩ | ⟨a', ha⟩ <;>
        rcases Nat.even_or_odd b with ⟨b', hb⟩ | ⟨b', hb⟩ <;>
          subst ha hb
      · -- even + even
        rw [show a' + a' = 2 * a' from (two_mul a').symm,
          show b' + b' = 2 * b' from (two_mul b').symm,
          show 2 * a' + 2 * b' = 2 * (a' + b') by ring,
          binaryWeight_two_mul, binaryWeight_two_mul, binaryWeight_two_mul]
        exact ih a' (by omega) b'
      · -- even + odd
        rw [show a' + a' = 2 * a' from (two_mul a').symm,
          show 2 * a' + (2 * b' + 1) = 2 * (a' + b') + 1 by ring,
          binaryWeight_two_mul, binaryWeight_two_mul_add_one,
          binaryWeight_two_mul_add_one]
        have := ih a' (by omega) b'
        omega
      · -- odd + even
        rw [show 2 * a' + 1 + (b' + b') = 2 * (a' + b') + 1 by ring,
          show b' + b' = 2 * b' from (two_mul b').symm,
          binaryWeight_two_mul_add_one, binaryWeight_two_mul_add_one,
          binaryWeight_two_mul]
        have := ih a' (by omega) b'
        omega
      · -- odd + odd: a carry occurs, and the successor law absorbs it.
        rw [show 2 * a' + 1 + (2 * b' + 1) = 2 * (a' + b' + 1) by ring,
          binaryWeight_two_mul, binaryWeight_two_mul_add_one,
          binaryWeight_two_mul_add_one]
        have h1 := binaryWeight_succ_le (a' + b')
        have h2 := ih a' (by omega) b'
        omega

/-- Adjacent Thue--Morse signs read the ruler sequence: the product of the
signs at `n` and `n + 1` is `(-1) ^ (ν₂(n + 1) + 1)`. -/
theorem thueMorseSign_mul_succ (n : ℕ) :
    thueMorseSign n * thueMorseSign (n + 1) =
      (-1 : ℤ) ^ (padicValNat 2 (n + 1) + 1) := by
  have h := binaryWeight_succ_add_padicValNat n
  rw [thueMorseSign, thueMorseSign, ← pow_add]
  exact neg_one_pow_eq_of_add_even
    (c := binaryWeight n + 1) (by omega)

/-- The successor recursion for the Thue--Morse sign in ruler form. -/
theorem thueMorseSign_succ_eq (n : ℕ) :
    thueMorseSign (n + 1) =
      (-1 : ℤ) ^ (padicValNat 2 (n + 1) + 1) * thueMorseSign n := by
  have h := binaryWeight_succ_add_padicValNat n
  rw [thueMorseSign, thueMorseSign, ← pow_add]
  exact neg_one_pow_eq_of_add_even
    (c := binaryWeight n + 1) (by omega)

/-- **Ruler-product formula.**  The Thue--Morse sign telescopes into a
product over the ruler sequence: `ε n = ∏_{k=1}^{n} (-1) ^ (ν₂(k) + 1)`. -/
theorem thueMorseSign_eq_prod_ruler (n : ℕ) :
    thueMorseSign n =
      ∏ k ∈ range n, (-1 : ℤ) ^ (padicValNat 2 (k + 1) + 1) := by
  induction n with
  | zero => simp [thueMorseSign, binaryWeight]
  | succ n ih =>
      rw [prod_range_succ, ← ih, thueMorseSign_succ_eq, mul_comm]

/-! ## The Catalan valuation -/

/-- **Catalan valuation.**  The two-adic valuation of the `n`-th Catalan
number is one less than the binary weight of `n + 1`.  In particular a
Catalan number is odd exactly when `n + 1` is a power of two. -/
theorem catalan_padicValNat_two_add_one (n : ℕ) :
    padicValNat 2 (catalan n) + 1 = binaryWeight (n + 1) := by
  have hmul : (n + 1) * catalan n = (2 * n).choose n := by
    simpa [Nat.centralBinom] using succ_mul_catalan_eq_centralBinom n
  have hcat : catalan n ≠ 0 := by
    intro h0
    have hzero := succ_mul_catalan_eq_centralBinom n
    rw [h0, Nat.mul_zero] at hzero
    exact absurd hzero.symm (Nat.centralBinom_pos n).ne'
  have hval : padicValNat 2 (n + 1) + padicValNat 2 (catalan n) =
      binaryWeight n := by
    rw [← padicValNat.mul (p := 2) (by omega) hcat, hmul,
      centralChoose_padicValNat_two]
  have hsucc := binaryWeight_succ_add_padicValNat n
  omega

/-- The sign of a successor read from a single Catalan number. -/
theorem thueMorseSign_succ_eq_neg_catalan (n : ℕ) :
    thueMorseSign (n + 1) = -(-1 : ℤ) ^ padicValNat 2 (catalan n) := by
  have h := catalan_padicValNat_two_add_one n
  rw [thueMorseSign, ← h, pow_succ]
  ring

/-! ## The borrow cocycle -/

/-- Additive form of Kummer's theorem at two: the valuation of the binomial
coefficient balances the binary-weight books of an addition.  This is the
truncation-free companion of `addChoose_padicValNat_two`. -/
theorem binaryWeight_add_addChoose_padicValNat (a b : ℕ) :
    binaryWeight (a + b) + padicValNat 2 ((a + b).choose a) =
      binaryWeight a + binaryWeight b := by
  have htrunc := addChoose_padicValNat_two a b
  have hle := binaryWeight_add_le a b
  omega

/-- **Borrow form of Kummer's theorem.**  For `b ≤ a`, the two-adic
valuation of `a.choose b` counts the borrows of the subtraction `a - b`,
with propagation. -/
theorem subChoose_padicValNat_two_add (a b : ℕ) (h : b ≤ a) :
    binaryWeight a + padicValNat 2 (a.choose b) =
      binaryWeight b + binaryWeight (a - b) := by
  have hthis := binaryWeight_add_addChoose_padicValNat b (a - b)
  rw [show b + (a - b) = a by omega] at hthis
  omega

/-- **Subtraction cocycle.**  The Thue--Morse sign of a difference carries
the same binomial-valuation correction as the sign of a sum. -/
theorem thueMorseSign_sub_valuation (a b : ℕ) (h : b ≤ a) :
    thueMorseSign (a - b) =
      thueMorseSign a * thueMorseSign b *
        (-1 : ℤ) ^ padicValNat 2 (a.choose b) := by
  have hsum := subChoose_padicValNat_two_add a b h
  rw [thueMorseSign, thueMorseSign, thueMorseSign, ← pow_add, ← pow_add]
  exact neg_one_pow_eq_of_add_even
    (c := binaryWeight a + padicValNat 2 (a.choose b)) (by omega)

end Fabius
