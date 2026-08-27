import FabiusFunction.ThueMorseValuation
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The arithmetic of dyadic zero multiplicities

For a positive integer `n`, the integer sinc product underlying the Rvachev
Fourier image has zero multiplicity

`a(n) = 1 + ν₂(n)`.

This module isolates the reusable arithmetic of that sequence from its
analytic applications.  The definition is total because Lean functions on
natural numbers are total, but every theorem that interprets the argument as
a zero explicitly assumes or constructs a positive index; no mathematical
meaning is assigned to the placeholder value at `n = 0`.

The main results are:

* `dyadicZeroMultiplicity_two_mul` and
  `dyadicZeroMultiplicity_two_mul_add_one`, the even/odd recurrences;
* `dyadicZeroMultiplicity_two_pow_mul`, the simultaneous extraction of an
  arbitrary dyadic factor;
* `sum_dyadicZeroMultiplicity_add_binaryWeight`, the truncation-free exact
  prefix law `∑_{n=1}^N a(n) + w(N) = 2N`;
* `neg_one_pow_dyadicZeroMultiplicity` and
  `neg_one_pow_sum_dyadicZeroMultiplicity`, the local and integrated
  Thue--Morse parity bridges;
* `card_dyadicZeroMultiplicity_ge_succ` and
  `card_dyadicZeroMultiplicity_eq_succ`, the exact finite distribution;
* `dyadicZeroMultiplicity_mul_of_coprime`, multiplicativity on positive
  coprime inputs.

All identities are finite.  In particular, the summatory formula is proved
directly from the successor law for binary weight rather than routed through
factorials or through the analytic lobe-counting API.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Definition and dyadic recurrences -/

/-- The arithmetic multiplicity `1 + ν₂(n)` attached to a positive
integer zero.  The value at `0` is only the totalization of this formula;
the zero-multiplicity API below uses positive arguments. -/
def dyadicZeroMultiplicity (n : ℕ) : ℕ :=
  padicValNat 2 n + 1

/-- Every positive-index dyadic zero has positive multiplicity. -/
theorem dyadicZeroMultiplicity_pos (n : ℕ) (_hn : 1 ≤ n) :
    1 ≤ dyadicZeroMultiplicity n := by
  simp [dyadicZeroMultiplicity]

/-- The first positive zero is simple. -/
@[simp] theorem dyadicZeroMultiplicity_one :
    dyadicZeroMultiplicity 1 = 1 := by
  rw [dyadicZeroMultiplicity,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 1)]

/-- Doubling a positive index raises its dyadic zero multiplicity by one. -/
theorem dyadicZeroMultiplicity_two_mul (n : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity (2 * n) = dyadicZeroMultiplicity n + 1 := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp only [dyadicZeroMultiplicity,
    padicValNat_base_mul (p := 2) (by omega) hn0]
  omega

/-- Every positive odd index is a simple zero. -/
@[simp] theorem dyadicZeroMultiplicity_two_mul_add_one (n : ℕ) :
    dyadicZeroMultiplicity (2 * n + 1) = 1 := by
  rw [dyadicZeroMultiplicity,
    padicValNat.eq_zero_of_not_dvd (Nat.not_two_dvd_bit1 n)]

/-- Extracting `r` factors of two from a positive index raises its zero
multiplicity by exactly `r`. -/
theorem dyadicZeroMultiplicity_two_pow_mul (r n : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity (2 ^ r * n) = dyadicZeroMultiplicity n + r := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp only [dyadicZeroMultiplicity,
    padicValNat_base_pow_mul (p := 2) (by omega) hn0 r]
  omega

/-- A power of two has multiplicity one more than its exponent. -/
@[simp] theorem dyadicZeroMultiplicity_two_pow (r : ℕ) :
    dyadicZeroMultiplicity (2 ^ r) = r + 1 := by
  simp [dyadicZeroMultiplicity,
    padicValNat_base_pow (p := 2) (by omega)]

/-- A positive index has multiplicity at least `r + 1` exactly when it is
divisible by `2 ^ r`.  This zero-based form avoids truncated subtraction in
both the statement and its counting consequences. -/
theorem dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
    (n r : ℕ) (hn : 1 ≤ n) :
    r + 1 ≤ dyadicZeroMultiplicity n ↔ 2 ^ r ∣ n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hval := padicValNat_dvd_iff_le_of_ne_one
    (p := 2) (by omega) (a := n) (n := r) hn0
  rw [dyadicZeroMultiplicity]
  constructor
  · intro h
    exact hval.mpr (by omega)
  · intro h
    have := hval.mp h
    omega

/-- A positive index has multiplicity exactly `r + 1` precisely when
`2 ^ r`, but not `2 ^ (r + 1)`, divides it. -/
theorem dyadicZeroMultiplicity_eq_succ_iff
    (n r : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity n = r + 1 ↔
      2 ^ r ∣ n ∧ ¬2 ^ (r + 1) ∣ n := by
  constructor
  · intro h
    constructor
    · exact (dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd n r hn).mp
        (by omega)
    · intro hnext
      have := (dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
        n (r + 1) hn).mpr hnext
      omega
  · rintro ⟨hr, hnext⟩
    have hlo := (dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd n r hn).mpr hr
    have hnhi : ¬((r + 1) + 1 ≤ dyadicZeroMultiplicity n) := by
      intro hhi
      exact hnext ((dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
        n (r + 1) hn).mp hhi)
    omega

/-! ## Exact prefix arithmetic -/

/-- **Exact prefix law, without natural subtraction.**  The positive-index
multiplicities through `N` and the binary weight of `N` balance exactly:
`∑_{k < N} a(k+1) + w(N) = 2N`.

The proof is the discrete integral of
`binaryWeight_succ_add_padicValNat`: each successor step contributes the
new multiplicity while the binary-weight remainder records the erased
trailing one-bits. -/
theorem sum_dyadicZeroMultiplicity_add_binaryWeight (N : ℕ) :
    (∑ k ∈ range N, dyadicZeroMultiplicity (k + 1)) + binaryWeight N =
      2 * N := by
  induction N with
  | zero => simp [dyadicZeroMultiplicity, binaryWeight]
  | succ N ih =>
      rw [sum_range_succ]
      have hsucc := binaryWeight_succ_add_padicValNat N
      simp only [dyadicZeroMultiplicity] at ih ⊢
      omega

/-- Subtraction form of the exact prefix law:
`∑_{n=1}^N a(n) = 2N - w(N)`.  The additive theorem
`sum_dyadicZeroMultiplicity_add_binaryWeight` is preferable for further
natural-number rearrangements. -/
theorem sum_dyadicZeroMultiplicity_eq (N : ℕ) :
    ∑ k ∈ range N, dyadicZeroMultiplicity (k + 1) =
      2 * N - binaryWeight N := by
  have h := sum_dyadicZeroMultiplicity_add_binaryWeight N
  omega

/-! ## Thue--Morse parity -/

/-- **Local parity bridge.**  At a positive index `n`, the parity of its
dyadic zero multiplicity is the discrete multiplicative derivative of the
Thue--Morse sign. -/
theorem neg_one_pow_dyadicZeroMultiplicity (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ℤ) ^ dyadicZeroMultiplicity n =
      thueMorseSign (n - 1) * thueMorseSign n := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h := (thueMorseSign_mul_succ (n - 1)).symm
  rw [hpred] at h
  simpa only [dyadicZeroMultiplicity] using h

/-- **Integrated parity bridge.**  The parity of the total positive zero
multiplicity through `N` is the `N`-th Thue--Morse sign. -/
theorem neg_one_pow_sum_dyadicZeroMultiplicity (N : ℕ) :
    (-1 : ℤ) ^ (∑ k ∈ range N, dyadicZeroMultiplicity (k + 1)) =
      thueMorseSign N := by
  calc
    (-1 : ℤ) ^ (∑ k ∈ range N, dyadicZeroMultiplicity (k + 1)) =
        ∏ k ∈ range N, (-1 : ℤ) ^ dyadicZeroMultiplicity (k + 1) :=
      (prod_pow_eq_pow_sum (range N)
        (fun k => dyadicZeroMultiplicity (k + 1)) (-1 : ℤ)).symm
    _ = thueMorseSign N := by
      simpa only [dyadicZeroMultiplicity] using
        (thueMorseSign_eq_prod_ruler N).symm

/-! ## Exact finite distribution -/

/-- Among `1, …, N`, exactly `⌊N / 2^r⌋` indices have dyadic zero
multiplicity at least `r + 1`. -/
theorem card_dyadicZeroMultiplicity_ge_succ (N r : ℕ) :
    ((range N).filter
      (fun k => r + 1 ≤ dyadicZeroMultiplicity (k + 1))).card =
        N / 2 ^ r := by
  rw [← Nat.card_multiples N (2 ^ r)]
  apply congrArg Finset.card
  ext k
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hk, hmult⟩
    exact ⟨hk, (dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
      (k + 1) r (by omega)).mp hmult⟩
  · rintro ⟨hk, hdvd⟩
    exact ⟨hk, (dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
      (k + 1) r (by omega)).mpr hdvd⟩

/-- Among `1, …, N`, the number of indices of exact dyadic zero
multiplicity `r + 1` is
`⌊N / 2^r⌋ - ⌊N / 2^(r+1)⌋`. -/
theorem card_dyadicZeroMultiplicity_eq_succ (N r : ℕ) :
    ((range N).filter
      (fun k => dyadicZeroMultiplicity (k + 1) = r + 1)).card =
        N / 2 ^ r - N / 2 ^ (r + 1) := by
  let lower := (range N).filter
    (fun k => r + 1 ≤ dyadicZeroMultiplicity (k + 1))
  let higher := (range N).filter
    (fun k => (r + 1) + 1 ≤ dyadicZeroMultiplicity (k + 1))
  have hsubset : higher ⊆ lower := by
    intro k hk
    simp only [higher, lower, mem_filter] at hk ⊢
    exact ⟨hk.1, by omega⟩
  have hexact :
      (range N).filter
          (fun k => dyadicZeroMultiplicity (k + 1) = r + 1) =
        lower \ higher := by
    ext k
    simp only [lower, higher, mem_filter, mem_sdiff, mem_range]
    omega
  rw [hexact, card_sdiff_of_subset hsubset]
  change lower.card - higher.card = _
  rw [show lower.card = N / 2 ^ r by
      exact card_dyadicZeroMultiplicity_ge_succ N r,
    show higher.card = N / 2 ^ (r + 1) by
      exact card_dyadicZeroMultiplicity_ge_succ N (r + 1)]

/-! ## Multiplicativity -/

/-- The dyadic zero-multiplicity sequence is multiplicative on positive
coprime inputs.  Coprimality ensures that at most one input has a nonzero
two-adic valuation, converting additivity of valuations into multiplication
of `1 + ν₂`. -/
theorem dyadicZeroMultiplicity_mul_of_coprime
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : m.Coprime n) :
    dyadicZeroMultiplicity (m * n) =
      dyadicZeroMultiplicity m * dyadicZeroMultiplicity n := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hzero : padicValNat 2 m = 0 ∨ padicValNat 2 n = 0 := by
    by_cases heven : 2 ∣ m
    · right
      apply padicValNat.eq_zero_of_not_dvd
      intro heven'
      have hgcd : 2 ∣ Nat.gcd m n := Nat.dvd_gcd heven heven'
      rw [hcop.gcd_eq_one] at hgcd
      norm_num at hgcd
    · exact Or.inl (padicValNat.eq_zero_of_not_dvd heven)
  rcases hzero with hzero | hzero
  · simp only [dyadicZeroMultiplicity, padicValNat.mul hm0 hn0,
      hzero, zero_add, one_mul]
  · simp only [dyadicZeroMultiplicity, padicValNat.mul hm0 hn0,
      hzero, add_zero, mul_one]

end Fabius
