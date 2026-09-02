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

/-- The evil enumeration lands on evil numbers. -/
@[simp] theorem thueMorseBit_evilEnum (n : ℕ) :
    thueMorseBit (evilEnum n) = 0 := by
  rw [evilEnum]
  rcases Nat.eq_zero_or_pos (thueMorseBit n) with h | h
  · rw [h, Nat.add_zero, thueMorseBit_two_mul, h]
  · have hb := thueMorseBit_le_one n
    have h1 : thueMorseBit n = 1 := by omega
    rw [h1, thueMorseBit_two_mul_add_one, h1]

/-- The odious enumeration lands on odious numbers. -/
@[simp] theorem thueMorseBit_odiousEnum (n : ℕ) :
    thueMorseBit (odiousEnum n) = 1 := by
  rw [odiousEnum]
  rcases Nat.eq_zero_or_pos (thueMorseBit n) with h | h
  · rw [h, Nat.sub_zero, thueMorseBit_two_mul_add_one, h]
  · have hb := thueMorseBit_le_one n
    have h1 : thueMorseBit n = 1 := by omega
    rw [h1, show 2 * n + 1 - 1 = 2 * n by omega, thueMorseBit_two_mul, h1]

/-- Every evil number is hit by the evil enumeration, at index `m / 2`. -/
theorem evilEnum_div_two (m : ℕ) (h : thueMorseBit m = 0) :
    evilEnum (m / 2) = m := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
  · rw [show k + k = 2 * k from (two_mul k).symm] at h ⊢
    rw [thueMorseBit_two_mul] at h
    rw [evilEnum, Nat.mul_div_cancel_left k (by norm_num), h]
    omega
  · rw [thueMorseBit_two_mul_add_one] at h
    have hb := thueMorseBit_le_one k
    have h1 : thueMorseBit k = 1 := by omega
    rw [evilEnum, show (2 * k + 1) / 2 = k by omega, h1]

/-- Every odious number is hit by the odious enumeration, at `m / 2`. -/
theorem odiousEnum_div_two (m : ℕ) (h : thueMorseBit m = 1) :
    odiousEnum (m / 2) = m := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
  · rw [show k + k = 2 * k from (two_mul k).symm] at h ⊢
    rw [thueMorseBit_two_mul] at h
    rw [odiousEnum, Nat.mul_div_cancel_left k (by norm_num), h]
    omega
  · rw [thueMorseBit_two_mul_add_one] at h
    have hb := thueMorseBit_le_one k
    have h0 : thueMorseBit k = 0 := by omega
    rw [odiousEnum, show (2 * k + 1) / 2 = k by omega, h0]
    omega

/-- The evil enumeration is strictly monotone. -/
theorem evilEnum_strictMono : StrictMono evilEnum := by
  intro a b hab
  have ha := thueMorseBit_le_one a
  have hb := thueMorseBit_le_one b
  rw [evilEnum, evilEnum]
  omega

/-- The odious enumeration is strictly monotone. -/
theorem odiousEnum_strictMono : StrictMono odiousEnum := by
  intro a b hab
  have ha := thueMorseBit_le_one a
  have hb := thueMorseBit_le_one b
  rw [odiousEnum, odiousEnum]
  omega

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
  rw [show evilEnum (evilEnum n) =
      2 * evilEnum n + thueMorseBit (evilEnum n) from rfl,
    thueMorseBit_evilEnum, Nat.add_zero]

/-- Composition laws: an odious index below the evil enumeration. -/
theorem odiousEnum_evilEnum (n : ℕ) :
    odiousEnum (evilEnum n) = 2 * evilEnum n + 1 := by
  rw [show odiousEnum (evilEnum n) =
      2 * evilEnum n + 1 - thueMorseBit (evilEnum n) from rfl,
    thueMorseBit_evilEnum, Nat.sub_zero]

/-- Composition laws: the evil enumeration of an odious index. -/
theorem evilEnum_odiousEnum (n : ℕ) :
    evilEnum (odiousEnum n) = 2 * odiousEnum n + 1 := by
  rw [show evilEnum (odiousEnum n) =
      2 * odiousEnum n + thueMorseBit (odiousEnum n) from rfl,
    thueMorseBit_odiousEnum]

/-- Composition laws: an odious index doubles cleanly. -/
theorem odiousEnum_odiousEnum (n : ℕ) :
    odiousEnum (odiousEnum n) = 2 * odiousEnum n := by
  rw [show odiousEnum (odiousEnum n) =
      2 * odiousEnum n + 1 - thueMorseBit (odiousEnum n) from rfl,
    thueMorseBit_odiousEnum]
  omega

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
