import FabiusFunction.ThueMorseValuation
import Mathlib.Data.Nat.Log

/-!
# Digit, floor, and bit-product formulas for the Thue--Morse sign

The formula atlas's digit chapter expresses the binary weight, and hence the
Thue--Morse sign, through floors and individual bits.  This module proves its
finite statements:

* `binaryWeight n ≤ n`, and the additive Legendre formula
  `binaryWeight n + padicValNat 2 n.factorial = n`;
* the floor-sum forms `binaryWeight n + ∑_{i=1}^{b-1} n / 2^i = n` and
  `∑_{j<m} n / 2^j + binaryWeight n = 2n`, truncation-free versions of
  `∑ ⌊n/2^i⌋ = n - w(n)`;
* the `testBit` bridge `binaryWeight n = ∑_{j<m} (n.testBit j).toNat`;
* the digit product `ε n = ∏_{j<m} (1 - 2·b_j(n))` and the floor-parity
  formula `ε n = (-1) ^ (∑_{j<m} n / 2^j)`.

All sums are finite; hypotheses `Nat.log 2 n < b` or `n < 2^m` say only
that the truncation window is wide enough to see every digit.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Weight versus size -/

/-- The binary weight of `n` is at most `n`. -/
theorem binaryWeight_le_self (n : ℕ) : binaryWeight n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [binaryWeight]
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
      · rw [show k + k = 2 * k from (two_mul k).symm, binaryWeight_two_mul]
        have := ih k (by omega)
        omega
      · rw [binaryWeight_two_mul_add_one]
        have := ih k (by omega)
        omega

/-- **Additive Legendre formula.**  The binary weight and the two-adic
valuation of the factorial partition `n` exactly. -/
theorem binaryWeight_add_padicValNat_factorial (n : ℕ) :
    binaryWeight n + padicValNat 2 n.factorial = n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := binaryWeight_le_self n
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  rw [show (Nat.digits 2 n).sum = binaryWeight n from rfl] at h
  omega

/-! ## Floor sums -/

/-- **Legendre's floor sum.**  The dyadic floors `n / 2, n / 4, …` sum to
`n - w(n)`; stated additively. -/
theorem binaryWeight_add_sum_div_two_pow (n b : ℕ) (hb : Nat.log 2 n < b) :
    binaryWeight n + ∑ i ∈ Ico 1 b, n / 2 ^ i = n := by
  have hfact := Nat.Prime.factorization_factorial (p := 2) Nat.prime_two hb
  have hval : (n.factorial.factorization) 2 = padicValNat 2 n.factorial :=
    Nat.factorization_def _ Nat.prime_two
  have hleg := binaryWeight_add_padicValNat_factorial n
  omega

/-- The complete dyadic floor sum, including the trivial index `j = 0`,
counts `n` twice minus the binary weight; stated additively. -/
theorem sum_div_two_pow_add_binaryWeight (n m : ℕ) (hm : Nat.log 2 n < m) :
    ∑ j ∈ range m, n / 2 ^ j + binaryWeight n = 2 * n := by
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
  have hsplit : ∑ j ∈ range m, n / 2 ^ j =
      n / 2 ^ 0 + ∑ j ∈ Ico 1 m, n / 2 ^ j := by
    rw [Finset.range_eq_Ico, ← Finset.sum_eq_sum_Ico_succ_bot hm0]
  have hIco := binaryWeight_add_sum_div_two_pow n m hm
  simp only [pow_zero, Nat.div_one] at hsplit
  omega

/-- **Floor-parity formula.**  The Thue--Morse sign is `-1` raised to the
complete dyadic floor sum. -/
theorem thueMorseSign_eq_neg_one_pow_sum_div (n m : ℕ)
    (hm : Nat.log 2 n < m) :
    thueMorseSign n = (-1 : ℤ) ^ (∑ j ∈ range m, n / 2 ^ j) := by
  have h := sum_div_two_pow_add_binaryWeight n m hm
  rw [thueMorseSign]
  exact neg_one_pow_eq_of_add_even (c := n) (by omega)

/-! ## Bits -/

/-- The binary weight is the number of set bits in any window wide enough
to contain them. -/
theorem binaryWeight_eq_sum_testBit (m : ℕ) :
    ∀ n : ℕ, n < 2 ^ m →
      binaryWeight n = ∑ j ∈ range m, (n.testBit j).toNat := by
  induction m with
  | zero =>
      intro n hn
      interval_cases n
      simp [binaryWeight]
  | succ m ih =>
      intro n hn
      have hdiv : n / 2 < 2 ^ m := by
        rw [pow_succ] at hn
        omega
      have hsucc : ∀ j : ℕ, n.testBit (j + 1) = (n / 2).testBit j := by
        intro j
        rw [Nat.testBit_succ]
      calc binaryWeight n
          = binaryWeight (n / 2) + (n.testBit 0).toNat := by
            rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
            · rw [show k + k = 2 * k from (two_mul k).symm,
                binaryWeight_two_mul, Nat.testBit_zero]
              simp [Nat.mul_div_cancel_left]
            · rw [binaryWeight_two_mul_add_one, Nat.testBit_zero]
              have : (2 * k + 1) / 2 = k := by omega
              simp [this]
        _ = ∑ j ∈ range m, ((n / 2).testBit j).toNat +
              (n.testBit 0).toNat := by rw [ih (n / 2) hdiv]
        _ = ∑ j ∈ range (m + 1), (n.testBit j).toNat := by
            rw [Finset.sum_range_succ']
            simp only [hsucc]

/-- **Digit-product formula.**  Each binary digit contributes an
independent sign factor `1 - 2·b_j(n) = (-1) ^ b_j(n)`. -/
theorem thueMorseSign_eq_prod_testBit (n m : ℕ) (h : n < 2 ^ m) :
    thueMorseSign n =
      ∏ j ∈ range m, (1 - 2 * ((n.testBit j).toNat : ℤ)) := by
  have hfactor : ∀ b : Bool, (1 - 2 * (b.toNat : ℤ)) = (-1) ^ b.toNat := by
    intro b
    cases b <;> norm_num
  calc thueMorseSign n
      = (-1 : ℤ) ^ (∑ j ∈ range m, (n.testBit j).toNat) := by
        rw [thueMorseSign, binaryWeight_eq_sum_testBit m n h]
    _ = ∏ j ∈ range m, ((-1 : ℤ)) ^ (n.testBit j).toNat := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ j ∈ range m, (1 - 2 * ((n.testBit j).toNat : ℤ)) := by
        exact Finset.prod_congr rfl fun j _ => (hfactor (n.testBit j)).symm

end Fabius
