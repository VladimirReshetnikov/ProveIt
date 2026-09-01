import FabiusFunction.FiniteQBinomialCore
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Cyclotomic factorization of `(q;q)_n` and of Gaussian coefficients

Since `X^j - 1 = ∏_{d ∣ j} Φ_d(X)`, the universal shifted factorial
`(X;X)_n = ∏_{j=1}^{n} (1 - X^j)` factors as

`(X;X)_n = (-1)^n ∏_{d=1}^{n} Φ_d(X)^{⌊n/d⌋}`,

the exponent `⌊n/d⌋` counting the multiples of `d` in `1, …, n`.  Dividing the
factorial identity `(X;X)_n = [n,k]_X (X;X)_k (X;X)_{n-k}` by the two smaller
products, in the integral domain `R[X]`, gives the **cyclotomic factorization
of the Gaussian coefficient**

`[n,k]_X = ∏_{d=1}^{n} Φ_d(X)^{e_d(n,k)}`,  `e_d(n,k) = ⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋ ∈ {0, 1}`.

## Main declarations

* `finiteQPochhammerIn_X_eq_prod_cyclotomic`: the factorization of `(X;X)_n`.
* `div_add_div_le_div`, `div_le_div_add_div_add_one`: `e_d ∈ {0,1}`.
* `gaussianBinomial_X_eq_prod_cyclotomic`: the factorization of `[n,k]_X`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-- `⌊k/d⌋ + ⌊(n-k)/d⌋ ≤ ⌊n/d⌋` for `k ≤ n`. -/
theorem div_add_div_le_div {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) :
    k / d + (n - k) / d ≤ n / d := by
  rw [Nat.le_div_iff_mul_le hd, add_mul]
  have h1 := Nat.div_mul_le_self k d
  have h2 := Nat.div_mul_le_self (n - k) d
  omega

/-- `⌊n/d⌋ ≤ ⌊k/d⌋ + ⌊(n-k)/d⌋ + 1` for `k ≤ n`: the exponent `e_d(n,k)` is `0` or `1`. -/
theorem div_le_div_add_div_add_one {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) :
    n / d ≤ k / d + (n - k) / d + 1 := by
  have hk1 := Nat.div_add_mod k d
  have hk2 := Nat.div_add_mod (n - k) d
  have hr := Nat.mod_lt k hd
  have hs := Nat.mod_lt (n - k) hd
  have h : n < d * (k / d + (n - k) / d + 2) := by
    rw [mul_add, mul_add]
    omega
  have := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [mul_comm]; exact h)
  omega

/-- The index exchange behind the cyclotomic factorization: `d` divides `j + 1`
with `j < n` if and only if `j` is a multiple index of `d` and `1 ≤ d ≤ n`. -/
theorem mem_range_and_mem_divisors_iff (n j d : ℕ) :
    j ∈ range n ∧ d ∈ (j + 1).divisors ↔
      j ∈ (range n).filter (fun e => d ∣ e + 1) ∧ d ∈ Icc 1 n := by
  rw [mem_range, Nat.mem_divisors, mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨hj, hdj, -⟩
    exact ⟨⟨hj, hdj⟩, Nat.pos_of_dvd_of_pos hdj (Nat.succ_pos j),
      (Nat.le_of_dvd (Nat.succ_pos j) hdj).trans hj⟩
  · rintro ⟨⟨hj, hdj⟩, -⟩
    exact ⟨hj, hdj, Nat.succ_ne_zero j⟩

variable {R : Type*} [CommRing R]

/-- **Cyclotomic factorization of the shifted factorial**:
`(X;X)_n = (-1)^n ∏_{d=1}^{n} Φ_d(X)^{⌊n/d⌋}` in `R[X]`. -/
theorem finiteQPochhammerIn_X_eq_prod_cyclotomic (n : ℕ) :
    finiteQPochhammerIn (X : R[X]) X n =
      (-1) ^ n * ∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d) := by
  have h1 : finiteQPochhammerIn (X : R[X]) X n =
      ∏ j ∈ range n, ((-1 : R[X]) * ∏ d ∈ (j + 1).divisors, cyclotomic d R) := by
    unfold finiteQPochhammerIn
    refine prod_congr rfl fun j _ => ?_
    rw [prod_cyclotomic_eq_X_pow_sub_one (Nat.succ_pos j) R, pow_succ']
    ring
  rw [h1, prod_mul_distrib, prod_const, card_range]
  congr 1
  rw [prod_comm' (t' := Icc 1 n) (s' := fun d => (range n).filter (fun e => d ∣ e + 1))
    (fun j d => mem_range_and_mem_divisors_iff n j d)]
  refine prod_congr rfl fun d _ => ?_
  rw [prod_const, Nat.card_multiples]

/-- The factorial identity `(X;X)_n = [n,k]_X (X;X)_k (X;X)_{n-k}` in `R[X]`. -/
theorem finiteQPochhammerIn_X_eq_gaussianBinomial_mul {n k : ℕ} (hk : k ≤ n) :
    finiteQPochhammerIn (X : R[X]) X n =
      gaussianBinomial (X : R[X]) n k *
        (finiteQPochhammerIn (X : R[X]) X k * finiteQPochhammerIn (X : R[X]) X (n - k)) := by
  have h1 := finiteQPochhammerIn_add (X : R[X]) X (n - k) k
  rw [Nat.sub_add_cancel hk] at h1
  have h2 := finiteQPochhammerIn_self_mul_gaussianBinomial (X : R[X]) hk
  rw [h1, ← pow_succ', ← h2]
  ring

/-- A cyclotomic product over `Icc 1 m` extends to `Icc 1 n` for `m ≤ n`, since the
exponents `⌊m/d⌋` vanish for `d > m`. -/
theorem prod_cyclotomic_pow_div_extend {m n : ℕ} (hmn : m ≤ n) :
    ∏ d ∈ Icc 1 m, cyclotomic d R ^ (m / d) = ∏ d ∈ Icc 1 n, cyclotomic d R ^ (m / d) := by
  refine prod_subset (Icc_subset_Icc_right hmn) fun d hd hdm => ?_
  rw [mem_Icc] at hd hdm
  rw [Nat.div_eq_of_lt (by omega), pow_zero]

/-- **Cyclotomic factorization of the Gaussian coefficient**, over an integral domain:
`[n,k]_X = ∏_{d=1}^{n} Φ_d(X)^{⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋}` for `k ≤ n`. -/
theorem gaussianBinomial_X_eq_prod_cyclotomic [IsDomain R] {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial (X : R[X]) n k =
      ∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d - k / d - (n - k) / d) := by
  -- the big product splits off the two smaller ones exponentwise
  have hexp : ∀ d ∈ Icc 1 n,
      n / d = (n / d - k / d - (n - k) / d) + (k / d + (n - k) / d) := by
    intro d hd
    have := div_add_div_le_div hk (mem_Icc.mp hd).1
    omega
  have hsplit : ∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d) =
      (∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d - k / d - (n - k) / d)) *
        ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun d hd => ?_
    rw [← pow_add, ← hexp d hd]
  -- the two smaller factorials, as one product over `Icc 1 n`
  have hsmall : finiteQPochhammerIn (X : R[X]) X k * finiteQPochhammerIn (X : R[X]) X (n - k) =
      (-1) ^ n * ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d) := by
    rw [finiteQPochhammerIn_X_eq_prod_cyclotomic, finiteQPochhammerIn_X_eq_prod_cyclotomic,
      prod_cyclotomic_pow_div_extend hk, prod_cyclotomic_pow_div_extend (Nat.sub_le n k)]
    have hP : (∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d)) *
        ∏ d ∈ Icc 1 n, cyclotomic d R ^ ((n - k) / d) =
        ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d) := by
      rw [← prod_mul_distrib]
      simp_rw [← pow_add]
    rw [← hP, show ((-1 : R[X]) ^ n) = (-1) ^ k * (-1) ^ (n - k) by
      rw [← pow_add, Nat.add_sub_of_le hk]]
    ring
  -- cancel the nonvanishing smaller product
  have hB : (∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun d _ => pow_ne_zero _ (cyclotomic_ne_zero d R)
  have hunit : ((-1 : R[X]) ^ n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have key : ((-1 : R[X]) ^ n * ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d)) *
        gaussianBinomial (X : R[X]) n k =
      ((-1 : R[X]) ^ n * ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d)) *
        ∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d - k / d - (n - k) / d) := by
    calc ((-1 : R[X]) ^ n * ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d)) *
          gaussianBinomial (X : R[X]) n k
        = gaussianBinomial (X : R[X]) n k *
            (finiteQPochhammerIn (X : R[X]) X k * finiteQPochhammerIn (X : R[X]) X (n - k)) := by
          rw [← hsmall]
          ring
      _ = finiteQPochhammerIn (X : R[X]) X n :=
          (finiteQPochhammerIn_X_eq_gaussianBinomial_mul hk).symm
      _ = (-1) ^ n * ((∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d - k / d - (n - k) / d)) *
            ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d)) := by
          rw [finiteQPochhammerIn_X_eq_prod_cyclotomic, hsplit]
      _ = ((-1 : R[X]) ^ n * ∏ d ∈ Icc 1 n, cyclotomic d R ^ (k / d + (n - k) / d)) *
            ∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d - k / d - (n - k) / d) := by ring
  exact mul_left_cancel₀ (mul_ne_zero hunit hB) key

end Fabius
