import FabiusFunction.ThueMorseBinomialLog
import FabiusFunction.ThueMorseBooleanCube
import FabiusFunction.ThueMorseValuation

/-!
# Weight enumerators, evil and odious numbers, and XOR correlations

A dyadic block `{0, …, 2^m - 1}` is a Boolean cube: its binary weights are
distributed binomially, and the Thue--Morse sign is the alternating
character of that cube.  This module proves the atlas's enumerator chapter:

* the **weight enumerator** `∑_{n < 2^m} u ^ w(n) = (1 + u) ^ m` over any
  commutative semiring, and the count
  `#{n < 2^m : w(n) = r} = m.choose r`, extracted from the enumerator by a
  polynomial coefficient comparison;
* the **evil/odious enumerations**: `2n + τ(n)` and `2n + 1 - τ(n)` are the
  `n`-th numbers of even and odd binary weight, their difference is the
  Thue--Morse sign, and their compositions satisfy the four exact closure
  laws of the atlas;
* the **generic bit enumeration** `bitEnum b n`, the `n`-th integer
  whose Thue--Morse bit is `b`: the evil and odious enumerations are its
  instances `b = 0` and `b = 1`, and their eight mirrored theorems
  (bit value, surjectivity onto the bit class, strict monotonicity, the
  four composition laws) are each derived from one generic statement;
* the **bit/sign bridge** `thueMorseBit_eq_iff_thueMorseSign_eq` and
  `thueMorseBit_ne_iff_thueMorseSign_eq_neg`: equal bits are equal
  signs, distinct bits are opposite signs;
* the **XOR autocorrelation** `∑_{n < 2^m} ε(n) ε(n XOR a) = 2^m ε(a)` and
  the signed **Hamming-sphere sums**
  `∑_{w(n XOR a) = r} ε(n) = ε(a) (-1)^r m.choose r`.

Everything is finite and exact.  The enumerator proof is a direct induction
on the block level; the count is obtained by reading the enumerator in
`Polynomial ℕ` and comparing coefficients — the generating-function method
of the atlas, executed literally.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The weight enumerator of a dyadic block -/

/-- **Weight distribution.**  A dyadic block of level `m` contains exactly
`m.choose r` integers of binary weight `r`.  Extracted from the general
weight enumerator `sum_pow_binaryWeight_eq_one_add_pow` by comparing
coefficients in `Polynomial ℕ`. -/
theorem card_filter_binaryWeight_eq (m r : ℕ) :
    #({n ∈ range (2 ^ m) | binaryWeight n = r}) = m.choose r := by
  classical
  have henum :=
    sum_pow_binaryWeight_eq_one_add_pow (Polynomial.X : Polynomial ℕ) m
  have hcoeff := congrArg (fun p : Polynomial ℕ => p.coeff r) henum
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    Polynomial.coeff_one_add_X_pow, Nat.cast_id] at hcoeff
  rw [Finset.card_filter, ← hcoeff]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : binaryWeight n = r
  · simp [h]
  · simp [eq_comm]

/-! ## Evil and odious numbers -/

/-- The `n`-th evil number (even binary weight), in increasing order. -/
def evilEnum (n : ℕ) : ℕ :=
  2 * n + thueMorseBit n

/-- The `n`-th odious number (odd binary weight), in increasing order. -/
def odiousEnum (n : ℕ) : ℕ :=
  2 * n + 1 - thueMorseBit n

/-- The Thue--Morse bit of an even index. -/
theorem thueMorseBit_two_mul (n : ℕ) :
    thueMorseBit (2 * n) = thueMorseBit n := by
  simp only [thueMorseBit, binaryWeight_two_mul]

/-- The Thue--Morse bit of an odd index. -/
theorem thueMorseBit_two_mul_add_one (n : ℕ) :
    thueMorseBit (2 * n + 1) = 1 - thueMorseBit n := by
  simp only [thueMorseBit, binaryWeight_two_mul_add_one]
  omega

/-! ### Bits and signs -/

/-- Two indices have equal Thue--Morse bits iff they have equal
Thue--Morse signs. -/
theorem thueMorseBit_eq_iff_thueMorseSign_eq (a b : ℕ) :
    thueMorseBit a = thueMorseBit b ↔
      thueMorseSign a = thueMorseSign b := by
  have ha := thueMorseSign_eq_one_sub_two_mul_bit a
  have hb := thueMorseSign_eq_one_sub_two_mul_bit b
  have ha1 := thueMorseBit_le_one a
  have hb1 := thueMorseBit_le_one b
  constructor <;> intro h <;> omega

/-- Two indices have distinct Thue--Morse bits iff their Thue--Morse
signs are opposite. -/
theorem thueMorseBit_ne_iff_thueMorseSign_eq_neg (a b : ℕ) :
    thueMorseBit a ≠ thueMorseBit b ↔
      thueMorseSign a = -thueMorseSign b := by
  have ha := thueMorseSign_eq_one_sub_two_mul_bit a
  have hb := thueMorseSign_eq_one_sub_two_mul_bit b
  have ha1 := thueMorseBit_le_one a
  have hb1 := thueMorseBit_le_one b
  constructor <;> intro h <;> omega

/-! ### The generic bit enumeration -/

/-- The `n`-th integer whose Thue--Morse bit is `b` (for `b ≤ 1`), in
increasing order: `2n` when `τ(n) = b`, else `2n + 1`.  The evil and
odious enumerations are the instances `b = 0` and `b = 1`
(`evilEnum_eq_bitEnum`, `odiousEnum_eq_bitEnum`). -/
def bitEnum (b n : ℕ) : ℕ :=
  if thueMorseBit n = b then 2 * n else 2 * n + 1

/-- `bitEnum b` doubles an index whose bit is `b`. -/
theorem bitEnum_of_thueMorseBit_eq {b m : ℕ} (h : thueMorseBit m = b) :
    bitEnum b m = 2 * m := by
  rw [bitEnum, if_pos h]

/-- `bitEnum b` doubles and increments an index whose bit is not `b`. -/
theorem bitEnum_of_thueMorseBit_ne {b m : ℕ} (h : thueMorseBit m ≠ b) :
    bitEnum b m = 2 * m + 1 := by
  rw [bitEnum, if_neg h]

/-- The evil enumeration is the bit enumeration at `b = 0`. -/
theorem evilEnum_eq_bitEnum (n : ℕ) : evilEnum n = bitEnum 0 n := by
  have hb := thueMorseBit_le_one n
  unfold evilEnum bitEnum
  split_ifs <;> omega

/-- The odious enumeration is the bit enumeration at `b = 1`. -/
theorem odiousEnum_eq_bitEnum (n : ℕ) : odiousEnum n = bitEnum 1 n := by
  have hb := thueMorseBit_le_one n
  unfold odiousEnum bitEnum
  split_ifs <;> omega

/-- The bit enumeration lands on indices of bit `b`. -/
theorem thueMorseBit_bitEnum {b : ℕ} (hb : b ≤ 1) (n : ℕ) :
    thueMorseBit (bitEnum b n) = b := by
  have hn := thueMorseBit_le_one n
  by_cases h : thueMorseBit n = b
  · rw [bitEnum_of_thueMorseBit_eq h, thueMorseBit_two_mul, h]
  · rw [bitEnum_of_thueMorseBit_ne h, thueMorseBit_two_mul_add_one]
    omega

/-- Every index of bit `b` is hit by the bit enumeration, at `m / 2`. -/
theorem bitEnum_div_two {b : ℕ} (m : ℕ) (h : thueMorseBit m = b) :
    bitEnum b (m / 2) = m := by
  rcases Nat.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  · rw [thueMorseBit_two_mul] at h
    rw [Nat.mul_div_cancel_left k (by norm_num),
      bitEnum_of_thueMorseBit_eq h]
  · rw [thueMorseBit_two_mul_add_one] at h
    have hk := thueMorseBit_le_one k
    have hne : thueMorseBit k ≠ b := by omega
    rw [show (2 * k + 1) / 2 = k by omega,
      bitEnum_of_thueMorseBit_ne hne]

/-- The bit enumeration is strictly monotone, for every `b`. -/
theorem bitEnum_strictMono (b : ℕ) : StrictMono (bitEnum b) := by
  intro x y hxy
  unfold bitEnum
  split_ifs <;> omega

/-- Composition law: the bit enumeration doubles its own values. -/
theorem bitEnum_bitEnum_self {b : ℕ} (hb : b ≤ 1) (n : ℕ) :
    bitEnum b (bitEnum b n) = 2 * bitEnum b n :=
  bitEnum_of_thueMorseBit_eq (thueMorseBit_bitEnum hb n)

/-- Composition law: the enumeration of any other bit doubles and
increments the values of `bitEnum b`. -/
theorem bitEnum_bitEnum_of_ne {b c : ℕ} (hb : b ≤ 1) (hcb : c ≠ b)
    (n : ℕ) : bitEnum c (bitEnum b n) = 2 * bitEnum b n + 1 := by
  apply bitEnum_of_thueMorseBit_ne
  rw [thueMorseBit_bitEnum hb]
  exact hcb.symm

/-- The composition law in one formula: `bitEnum c ∘ bitEnum b` doubles,
plus one exactly when `c ≠ b`. -/
theorem bitEnum_bitEnum {b : ℕ} (c : ℕ) (hb : b ≤ 1) (n : ℕ) :
    bitEnum c (bitEnum b n) =
      2 * bitEnum b n + (if c = b then 0 else 1) := by
  by_cases hcb : c = b
  · rw [if_pos hcb, Nat.add_zero, hcb, bitEnum_bitEnum_self hb]
  · rw [if_neg hcb, bitEnum_bitEnum_of_ne hb hcb]

/-! ### The evil and odious instances -/

/-- The evil enumeration lands on evil numbers. -/
@[simp] theorem thueMorseBit_evilEnum (n : ℕ) :
    thueMorseBit (evilEnum n) = 0 := by
  rw [evilEnum_eq_bitEnum]
  exact thueMorseBit_bitEnum (by norm_num) n

/-- The odious enumeration lands on odious numbers. -/
@[simp] theorem thueMorseBit_odiousEnum (n : ℕ) :
    thueMorseBit (odiousEnum n) = 1 := by
  rw [odiousEnum_eq_bitEnum]
  exact thueMorseBit_bitEnum (by norm_num) n

/-- Every evil number is hit by the evil enumeration, at index `m / 2`. -/
theorem evilEnum_div_two (m : ℕ) (h : thueMorseBit m = 0) :
    evilEnum (m / 2) = m := by
  rw [evilEnum_eq_bitEnum]
  exact bitEnum_div_two m h

/-- Every odious number is hit by the odious enumeration, at `m / 2`. -/
theorem odiousEnum_div_two (m : ℕ) (h : thueMorseBit m = 1) :
    odiousEnum (m / 2) = m := by
  rw [odiousEnum_eq_bitEnum]
  exact bitEnum_div_two m h

/-- The evil enumeration is strictly monotone. -/
theorem evilEnum_strictMono : StrictMono evilEnum := by
  have h : evilEnum = bitEnum 0 := funext evilEnum_eq_bitEnum
  rw [h]
  exact bitEnum_strictMono 0

/-- The odious enumeration is strictly monotone. -/
theorem odiousEnum_strictMono : StrictMono odiousEnum := by
  have h : odiousEnum = bitEnum 1 := funext odiousEnum_eq_bitEnum
  rw [h]
  exact bitEnum_strictMono 1

/-- The `n`-th odious number exceeds the `n`-th evil number by the
Thue--Morse sign: consecutive partners differ by exactly `ε(n)`. -/
theorem odiousEnum_sub_evilEnum (n : ℕ) :
    (odiousEnum n : ℤ) - evilEnum n = thueMorseSign n := by
  have hb := thueMorseBit_le_one n
  have hsign := thueMorseSign_eq_one_sub_two_mul_bit n
  rw [odiousEnum, evilEnum]
  have hcast : ((2 * n + 1 - thueMorseBit n : ℕ) : ℤ) =
      2 * n + 1 - thueMorseBit n := by
    push_cast [Nat.cast_sub (by omega : thueMorseBit n ≤ 2 * n + 1)]
    ring
  rw [hcast]
  push_cast
  omega

/-- The `n`-th evil and odious numbers sum to `4n + 1`. -/
theorem evilEnum_add_odiousEnum (n : ℕ) :
    evilEnum n + odiousEnum n = 4 * n + 1 := by
  have hb := thueMorseBit_le_one n
  rw [evilEnum, odiousEnum]
  omega

/-- Composition laws: an evil index doubles cleanly. -/
theorem evilEnum_evilEnum (n : ℕ) :
    evilEnum (evilEnum n) = 2 * evilEnum n := by
  simp only [evilEnum_eq_bitEnum]
  exact bitEnum_bitEnum_self (by norm_num) n

/-- Composition laws: an odious index below the evil enumeration. -/
theorem odiousEnum_evilEnum (n : ℕ) :
    odiousEnum (evilEnum n) = 2 * evilEnum n + 1 := by
  simp only [evilEnum_eq_bitEnum, odiousEnum_eq_bitEnum]
  exact bitEnum_bitEnum_of_ne (by norm_num) (by norm_num) n

/-- Composition laws: the evil enumeration of an odious index. -/
theorem evilEnum_odiousEnum (n : ℕ) :
    evilEnum (odiousEnum n) = 2 * odiousEnum n + 1 := by
  simp only [evilEnum_eq_bitEnum, odiousEnum_eq_bitEnum]
  exact bitEnum_bitEnum_of_ne (by norm_num) (by norm_num) n

/-- Composition laws: an odious index doubles cleanly. -/
theorem odiousEnum_odiousEnum (n : ℕ) :
    odiousEnum (odiousEnum n) = 2 * odiousEnum n := by
  simp only [odiousEnum_eq_bitEnum]
  exact bitEnum_bitEnum_self (by norm_num) n

/-! ## XOR autocorrelation and Hamming spheres -/

/-- **XOR autocorrelation.**  Shifting by XOR leaves only the constant
`ε(a)`: the sum over any dyadic block is `2^m ε(a)`.  No alignment
hypothesis is needed, because the character identity holds termwise. -/
theorem sum_thueMorseSign_mul_xor (m a : ℕ) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * thueMorseSign (n ^^^ a) =
      2 ^ m * thueMorseSign a := by
  have hterm : ∀ n : ℕ,
      thueMorseSign n * thueMorseSign (n ^^^ a) = thueMorseSign a := by
    intro n
    rw [thueMorseSign_xor, thueMorseSign_mul_cancel]
  rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Bitwise XOR does not leave a dyadic block: the bound of
`Nat.bitwise_lt_two_pow` specialized to XOR. -/
theorem xor_lt_two_pow {a b m : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m) :
    a ^^^ b < 2 ^ m :=
  Nat.bitwise_lt_two_pow ha hb

/-- **Signed Hamming spheres.**  Within a dyadic block containing `a`, the
signed count of the sphere of XOR-radius `r` around `a` is
`ε(a) (-1)^r m.choose r`: spheres inherit the sign of their center,
attenuated binomially. -/
theorem sum_thueMorseSign_hammingSphere (m a r : ℕ) (ha : a < 2 ^ m) :
    ∑ n ∈ {n ∈ range (2 ^ m) | binaryWeight (n ^^^ a) = r},
        thueMorseSign n =
      thueMorseSign a * (-1) ^ r * m.choose r := by
  classical
  -- Reindex by the involution `n ↦ n XOR a` of the block.
  have hinv : ∀ n : ℕ, n ^^^ a ^^^ a = n := by
    intro n
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have key : ∑ n ∈ {n ∈ range (2 ^ m) | binaryWeight (n ^^^ a) = r},
      thueMorseSign n =
      ∑ h ∈ {h ∈ range (2 ^ m) | binaryWeight h = r},
        thueMorseSign a * thueMorseSign h := by
    refine Finset.sum_equiv
      ⟨fun n => n ^^^ a, fun h => h ^^^ a, hinv, hinv⟩ ?_ ?_
    · intro n
      simp only [Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hn, hw⟩
        exact ⟨xor_lt_two_pow hn ha, hw⟩
      · rintro ⟨hn, hw⟩
        refine ⟨?_, hw⟩
        have := xor_lt_two_pow hn ha
        rwa [hinv] at this
    · intro n hn
      simp only [Equiv.coe_fn_mk]
      rw [thueMorseSign_xor]
      have hsq := thueMorseSign_mul_self a
      linear_combination (-(thueMorseSign n)) * hsq
  rw [key, ← Finset.mul_sum]
  have hval : ∀ h ∈ {h ∈ range (2 ^ m) | binaryWeight h = r},
      thueMorseSign h = (-1 : ℤ) ^ r := by
    intro h hh
    simp only [Finset.mem_filter] at hh
    rw [thueMorseSign, hh.2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_filter_binaryWeight_eq, nsmul_eq_mul]
  ring

end Fabius
