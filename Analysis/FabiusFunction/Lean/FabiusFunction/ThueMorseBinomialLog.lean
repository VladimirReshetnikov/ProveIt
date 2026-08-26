import FabiusFunction.DyadicClosedForm
import FabiusFunction.Parity
import Mathlib.Data.Nat.Log

/-!
# A binomial-logarithm formula for the Thue--Morse sequence

This module proves the Wolfram Language identity

`ThueMorse[n] = (1 + (-1)^Log2[n + 1 -
  Sum[(-1)^Binomial[n,k], {k,0,n}]]) / 2`.

The finite sum is interpreted in `ℤ`, since its summands are signs, and the
outer division is interpreted in `ℚ`.  The logarithm is represented by
`Nat.log2` only after proving that its argument is exactly the positive power
`2 ^ (binaryWeight n + 1)`.

The final sign lemmas are coefficient-facing forms of the same parity fact:
in an arbitrary ring, raising `-1` to `thueMorseBit r` is already the same as
raising it to the full binary weight.  This lets later real and complex series
share one exact algebraic bridge instead of reopening the modulo-two
definition.  The accompanying positivity and range lemmas make explicit that
the logarithm argument is never truncated by `Int.toNat` and that the bit is
indeed zero-one valued at every index, including `n = 0`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The signed sum `sum_{k=0}^n (-1)^(choose n k)`. -/
def signedBinomialParitySum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ Nat.choose n k

private lemma neg_one_pow_choose (n k : ℕ) :
    (-1 : ℤ) ^ Nat.choose n k =
      if Odd (Nat.choose n k) then -1 else 1 := by
  split_ifs with h
  · exact h.neg_one_pow
  · exact (Nat.not_odd_iff_even.mp h).neg_one_pow

/-- The signed sum is the row length minus twice the number of odd entries. -/
theorem signedBinomialParitySum_eq (n : ℕ) :
    signedBinomialParitySum n =
      (n + 1 : ℤ) - 2 * (oddBinomialIndices n).card := by
  rw [signedBinomialParitySum]
  simp_rw [neg_one_pow_choose]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, oddBinomialIndices]
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.range (n + 1)) (p := fun k => Odd (Nat.choose n k))
  simp only [Finset.card_range] at hc
  omega

/-- The integer inside `Log2` is exactly a positive power of two. -/
theorem thueMorseLogIntegerArgument_eq_two_pow (n : ℕ) :
    (n + 1 : ℤ) - signedBinomialParitySum n =
      (2 : ℤ) ^ (binaryWeight n + 1) := by
  rw [signedBinomialParitySum_eq, card_oddBinomialIndices]
  push_cast
  simp only [pow_succ]
  ring

/-- The integer logarithm argument is strictly positive, so the subsequent
conversion with `Int.toNat` loses no sign information. -/
theorem thueMorseLogIntegerArgument_pos (n : ℕ) :
    0 < (n + 1 : ℤ) - signedBinomialParitySum n := by
  rw [thueMorseLogIntegerArgument_eq_two_pow]
  positivity

/-- The natural argument of `Log2` in the Wolfram Language formula. -/
def thueMorseLog2Argument (n : ℕ) : ℕ :=
  Int.toNat ((n + 1 : ℤ) - signedBinomialParitySum n)

/-- The natural logarithm argument is the same exact power of two. -/
theorem thueMorseLog2Argument_eq (n : ℕ) :
    thueMorseLog2Argument n = 2 ^ (binaryWeight n + 1) := by
  rw [thueMorseLog2Argument, thueMorseLogIntegerArgument_eq_two_pow]
  rw [show (2 : ℤ) ^ (binaryWeight n + 1) =
      ((2 ^ (binaryWeight n + 1) : ℕ) : ℤ) by norm_num,
    Int.toNat_natCast]

/-- The natural argument supplied to `Nat.log2` is positive at every index. -/
theorem thueMorseLog2Argument_pos (n : ℕ) :
    0 < thueMorseLog2Argument n := by
  rw [thueMorseLog2Argument_eq]
  positivity

/-- Consequently the base-two logarithm in the formula is exact. -/
theorem log2_thueMorseLog2Argument (n : ℕ) :
    Nat.log2 (thueMorseLog2Argument n) = binaryWeight n + 1 := by
  rw [thueMorseLog2Argument_eq, Nat.log2_eq_log_two,
    Nat.log_pow (by norm_num)]

/-- The zero-one Thue--Morse sequence, matching Wolfram's `ThueMorse[n]`. -/
def thueMorseBit (n : ℕ) : ℕ :=
  binaryWeight n % 2

/-- The natural-valued Thue--Morse bit lies in the advertised range
`{0, 1}`. -/
theorem thueMorseBit_le_one (n : ℕ) : thueMorseBit n ≤ 1 := by
  unfold thueMorseBit
  have h := Nat.mod_lt (binaryWeight n) (by omega : 0 < 2)
  omega

/-- The zero-one sequence agrees with the existing signed convention. -/
theorem thueMorseSign_eq_one_sub_two_mul_bit (n : ℕ) :
    thueMorseSign n = 1 - 2 * (thueMorseBit n : ℤ) := by
  rcases Nat.even_or_odd (binaryWeight n) with heven | hodd
  · rw [thueMorseSign, thueMorseBit, Nat.even_iff.mp heven,
      heven.neg_one_pow]
    norm_num
  · rw [thueMorseSign, thueMorseBit, Nat.odd_iff.mp hodd,
      hodd.neg_one_pow]
    norm_num

/-- The zero-one Thue--Morse sequence carries bitwise xor to bitwise xor. -/
theorem thueMorseBit_xor (a b : ℕ) :
    thueMorseBit (a ^^^ b) = thueMorseBit a ^^^ thueMorseBit b := by
  have hsign := thueMorseSign_xor a b
  simp_rw [thueMorseSign_eq_one_sub_two_mul_bit] at hsign
  have ha : thueMorseBit a = 0 ∨ thueMorseBit a = 1 := by
    have ha_le := thueMorseBit_le_one a
    omega
  have hb : thueMorseBit b = 0 ∨ thueMorseBit b = 1 := by
    have hb_le := thueMorseBit_le_one b
    omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [ha, hb] at hsign ⊢ <;> omega

/-- Raising `-1` to the zero-one Thue--Morse bit is the same as raising it
to the full binary weight, in any ring.  This is the direct coefficient form
of the modulo-two definition. -/
theorem neg_one_pow_thueMorseBit_eq_binaryWeight
    {R : Type*} [Ring R] (r : ℕ) :
    (-1 : R) ^ thueMorseBit r = (-1 : R) ^ binaryWeight r := by
  rw [thueMorseBit]
  exact (neg_one_pow_eq_pow_mod_two (R := R) (binaryWeight r)).symm

/-- The Wolfram sign `(-1)^ThueMorse[r]` agrees with the repository's signed
Thue--Morse convention in **every** ring.

The argument needs nothing beyond `neg_one_pow_eq_pow_mod_two`, which Mathlib
states for `[Ring R]`, so no field, characteristic, order, or topological
hypothesis is involved.  The `ℚ`-valued specialization is
`neg_one_pow_thueMorseBit` in `FabiusRawQBinomialFormula`, which is retained
under its established name for its existing callers. -/
theorem neg_one_pow_thueMorseBit_ring {R : Type*} [Ring R] (r : ℕ) :
    (-1 : R) ^ thueMorseBit r = (thueMorseSign r : R) := by
  rw [neg_one_pow_thueMorseBit_eq_binaryWeight, thueMorseSign]
  push_cast
  rfl

/-- The parity form of the desired logarithmic expression. -/
theorem thueMorseBit_eq_sign_formula (n : ℕ) :
    (thueMorseBit n : ℚ) =
      (1 + (-1 : ℚ) ^ (binaryWeight n + 1)) / 2 := by
  rcases Nat.even_or_odd (binaryWeight n) with heven | hodd
  · rw [thueMorseBit, Nat.even_iff.mp heven,
      heven.add_one.neg_one_pow]
    norm_num
  · rw [thueMorseBit, Nat.odd_iff.mp hodd,
      hodd.add_one.neg_one_pow]
    norm_num

/-- The exact Wolfram Language identity.  Here `Nat.log2` is exact because
`thueMorseLogIntegerArgument_eq_two_pow` proves that its argument is a power
of two; the outer quotient is exact rational division. -/
theorem thueMorseBit_eq_log2_binomialParity_formula (n : ℕ) :
    (thueMorseBit n : ℚ) =
      (1 + (-1 : ℚ) ^ Nat.log2
        (Int.toNat ((n + 1 : ℤ) -
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ Nat.choose n k))) / 2 := by
  rw [← signedBinomialParitySum, ← thueMorseLog2Argument,
    log2_thueMorseLog2Argument]
  exact thueMorseBit_eq_sign_formula n

end Fabius
