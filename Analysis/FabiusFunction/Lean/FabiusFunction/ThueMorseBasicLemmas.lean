import FabiusFunction.Arithmetic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Basic lemmas on the Thue–Morse sign

The smallest facts about `binaryWeight` and `thueMorseSign` — the values
at `0`, `1`, `2`, the unit modulus in every ordered or normed ring, and
the two dyadic `atTop` limits — which the corpus had re-proved locally
(as private lemmas or inline `simp [thueMorseSign, binaryWeight]`
blocks) in more than a dozen modules.  They are collected here, in a
module importing only `Arithmetic`, so that every Thue–Morse module can
reach them without touching the foundational file.

* `binaryWeight_zero`, `binaryWeight_one`, `thueMorseSign_zero`,
  `thueMorseSign_one`, `thueMorseSign_two` — the first values.
* `abs_thueMorseSign_cast` — `|ε(n)| = 1` in any linearly ordered ring,
  with `abs_thueMorseSign` (over `ℤ`) and `abs_thueMorseSign_real` as
  the two instances the corpus uses.
* `thueMorseSign_eq_one_or_neg_one` — the sign is `±1`.
* `norm_thueMorseSign_cast` — `‖ε(n)‖ = 1` in any normed ring with
  `‖1‖ = 1`; `norm_thueMorseSign_complex` is the `ℂ` instance.
* `lt_two_pow_of_le` — `d ≤ j → d < 2^j`.
* `tendsto_two_pow_atTop`, `tendsto_two_mul_atTop` — the dyadic ladder
  and the doubling map tend to infinity.
-/

set_option autoImplicit false

open Filter

namespace Fabius

@[simp] theorem binaryWeight_zero : binaryWeight 0 = 0 := by
  simp [binaryWeight]

@[simp] theorem binaryWeight_one : binaryWeight 1 = 1 := by
  rw [binaryWeight, Nat.digits_def' one_lt_two one_pos]
  simp

@[simp] theorem thueMorseSign_zero : thueMorseSign 0 = 1 := by
  simp [thueMorseSign]

@[simp] theorem thueMorseSign_one : thueMorseSign 1 = -1 := by
  simp [thueMorseSign]

@[simp] theorem thueMorseSign_two : thueMorseSign 2 = -1 := by
  rw [thueMorseSign, binaryWeight, Nat.digits_def' one_lt_two two_pos]
  simp

/-- The Thue–Morse sign has absolute value one in every linearly ordered
ring. -/
theorem abs_thueMorseSign_cast {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] (n : ℕ) :
    |((thueMorseSign n : ℤ) : R)| = 1 := by
  rw [thueMorseSign]
  push_cast
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- `|ε(n)| = 1` over `ℤ`. -/
theorem abs_thueMorseSign (n : ℕ) : |thueMorseSign n| = 1 := by
  rw [thueMorseSign, abs_pow, abs_neg, abs_one, one_pow]

/-- `|ε(n)| = 1` over `ℝ`. -/
theorem abs_thueMorseSign_real (n : ℕ) : |(thueMorseSign n : ℝ)| = 1 :=
  abs_thueMorseSign_cast n

/-- The Thue–Morse sign is `1` or `-1`. -/
theorem thueMorseSign_eq_one_or_neg_one (n : ℕ) :
    thueMorseSign n = 1 ∨ thueMorseSign n = -1 :=
  (abs_eq zero_le_one).mp (abs_thueMorseSign n)

/-- The Thue–Morse sign has norm one in every normed ring with `‖1‖ = 1`. -/
theorem norm_thueMorseSign_cast {R : Type*} [NormedRing R] [NormOneClass R]
    (n : ℕ) : ‖((thueMorseSign n : ℤ) : R)‖ = 1 := by
  rw [thueMorseSign]
  push_cast
  rcases neg_one_pow_eq_or R (binaryWeight n) with h | h <;> simp [h]

/-- The Thue–Morse sign has norm one over `ℂ`. -/
theorem norm_thueMorseSign_complex (n : ℕ) :
    ‖(thueMorseSign n : ℂ)‖ = 1 :=
  norm_thueMorseSign_cast n

/-- `(-1)^a = (-1)^b` whenever `a + b` is even, in any monoid with a
distributive negation — the sign-collapse step of every parity identity
in the corpus (`ThueMorseValuation.neg_one_pow_eq_of_add_even` is the
`ℤ` instance). -/
theorem neg_one_pow_eq_of_add_eq_two_mul {R : Type*} [Monoid R]
    [HasDistribNeg R] {a b c : ℕ} (h : a + b = 2 * c) :
    ((-1 : R)) ^ a = (-1) ^ b := by
  have hab : ((-1 : R)) ^ a * (-1) ^ b = 1 := by
    rw [← pow_add, h, pow_mul, neg_one_sq, one_pow]
  have hbb : ((-1 : R)) ^ b * (-1) ^ b = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc ((-1 : R)) ^ a
      = (-1) ^ a * ((-1) ^ b * (-1) ^ b) := by rw [hbb, mul_one]
    _ = ((-1) ^ a * (-1) ^ b) * (-1) ^ b := by rw [mul_assoc]
    _ = (-1) ^ b := by rw [hab, one_mul]

/-- `d ≤ j` implies `d < 2^j`: every index below the exponent lies in
the dyadic block. -/
theorem lt_two_pow_of_le {d j : ℕ} (h : d ≤ j) : d < 2 ^ j :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right two_pos h)

/-- The dyadic ladder `m ↦ 2^m` tends to infinity. -/
theorem tendsto_two_pow_atTop : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
  tendsto_atTop_mono (fun m => (Nat.lt_two_pow_self (n := m)).le) tendsto_id

/-- The doubling map `n ↦ 2n` tends to infinity. -/
theorem tendsto_two_mul_atTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_mono (fun n => (by omega : n ≤ 2 * n)) tendsto_id

end Fabius
