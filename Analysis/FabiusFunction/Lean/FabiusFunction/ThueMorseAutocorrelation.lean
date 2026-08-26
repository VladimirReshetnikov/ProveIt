import FabiusFunction.ThueMorseEnumerators

/-!
# Finite autocorrelation of the Thue–Morse signs

The dyadic autocorrelation sums `A_m(k) = ∑_{n<2^m} ε(n)ε(n+k)` (with the
shifted index *not* reduced modulo the block) satisfy an exact two-scale
recursion which, after normalization by `2^m`, characterizes the limiting
autocorrelation measure of the Thue–Morse dynamical system.  This module
proves the finite layer in exact integer arithmetic:

* `thueMorseAutocorrelation_zero_shift` — `A_m(0) = 2^m`.
* `thueMorseAutocorrelation_succ_even` — `A_{m+1}(2r) = 2·A_m(r)`.
* `thueMorseAutocorrelation_succ_odd` —
  `A_{m+1}(2r+1) = -(A_m(r) + A_m(r+1))`.
* `three_mul_thueMorseAutocorrelation_one` — the closed value at shift
  one: `3·A_m(1) = -2^m - 2·(-1)^m`, whence `A_m(1)/2^m → -1/3`; and its
  shift-two companion `three_mul_thueMorseAutocorrelation_two`.

Everything is a finite sum manipulation through the two-scale sign laws
`ε(2j) = ε(j)`, `ε(2j+1) = -ε(j)`; no measure theory enters.  The
normalized limit `η(k) = lim A_m(k)/2^m` and its spectral consequences
remain analytic frontiers.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The finite Thue–Morse autocorrelation
`A_m(k) = ∑_{n<2^m} ε(n)·ε(n+k)`, unnormalized and unreduced. -/
def thueMorseAutocorrelation (m k : ℕ) : ℤ :=
  ∑ n ∈ range (2 ^ m), thueMorseSign n * thueMorseSign (n + k)

/-- Zero shift: `A_m(0) = 2^m`. -/
theorem thueMorseAutocorrelation_zero_shift (m : ℕ) :
    thueMorseAutocorrelation m 0 = 2 ^ m := by
  rw [thueMorseAutocorrelation]
  have hterm : ∀ n ∈ range (2 ^ m),
      thueMorseSign n * thueMorseSign (n + 0) = 1 := by
    intro n _
    rw [Nat.add_zero, thueMorseSign_mul_self]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
  ring

/-- Even shifts reduce scale: `A_{m+1}(2r) = 2·A_m(r)`. -/
theorem thueMorseAutocorrelation_succ_even (m r : ℕ) :
    thueMorseAutocorrelation (m + 1) (2 * r) =
      2 * thueMorseAutocorrelation m r := by
  rw [thueMorseAutocorrelation, thueMorseAutocorrelation,
    show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring,
    sum_range_two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * j + (2 * r) = 2 * (j + r) by ring, thueMorseSign_two_mul,
    thueMorseSign_two_mul,
    show 2 * j + 1 + 2 * r = 2 * (j + r) + 1 by ring,
    thueMorseSign_two_mul_add_one, thueMorseSign_two_mul_add_one]
  ring

/-- Odd shifts mix the two neighbors:
`A_{m+1}(2r+1) = -(A_m(r) + A_m(r+1))`. -/
theorem thueMorseAutocorrelation_succ_odd (m r : ℕ) :
    thueMorseAutocorrelation (m + 1) (2 * r + 1) =
      -(thueMorseAutocorrelation m r + thueMorseAutocorrelation m (r + 1)) := by
  rw [thueMorseAutocorrelation, thueMorseAutocorrelation,
    thueMorseAutocorrelation,
    show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring,
    sum_range_two_mul, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * j + (2 * r + 1) = 2 * (j + r) + 1 by ring,
    thueMorseSign_two_mul, thueMorseSign_two_mul_add_one,
    show 2 * j + 1 + (2 * r + 1) = 2 * (j + (r + 1)) by ring,
    thueMorseSign_two_mul_add_one, thueMorseSign_two_mul]
  ring

/-- The closed value at shift one: `3·A_m(1) = -2^m - 2·(-1)^m`.  After
normalization, `A_m(1)/2^m → -1/3`, the first nontrivial value of the
limiting Thue–Morse autocorrelation. -/
theorem three_mul_thueMorseAutocorrelation_one (m : ℕ) :
    3 * thueMorseAutocorrelation m 1 = -(2 ^ m) - 2 * (-1) ^ m := by
  induction m with
  | zero =>
      norm_num [thueMorseAutocorrelation, thueMorseSign, binaryWeight]
  | succ m ih =>
      have h := thueMorseAutocorrelation_succ_odd m 0
      rw [Nat.mul_zero, Nat.zero_add] at h
      rw [h, thueMorseAutocorrelation_zero_shift]
      have hp : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      have hn : ((-1 : ℤ)) ^ (m + 1) = -((-1) ^ m) := by rw [pow_succ]; ring
      linarith [ih]

/-- The closed value at shift two: `3·A_{m+1}(2) = -2^{m+1} - 4·(-1)^m`;
after normalization, `A_m(2)/2^m → -1/3` as well. -/
theorem three_mul_thueMorseAutocorrelation_two (m : ℕ) :
    3 * thueMorseAutocorrelation (m + 1) 2 =
      -(2 ^ (m + 1)) - 4 * (-1) ^ m := by
  have h := thueMorseAutocorrelation_succ_even m 1
  rw [Nat.mul_one] at h
  have h1 := three_mul_thueMorseAutocorrelation_one m
  have hp : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  rw [h]
  linarith [h1]

end Fabius
