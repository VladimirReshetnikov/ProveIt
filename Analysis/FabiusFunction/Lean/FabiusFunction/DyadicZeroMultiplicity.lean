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

The recurrences, the divisibility characterizations, the exact finite
distribution and multiplicativity hold verbatim at any base `p > 1`
(prime, for multiplicativity), and are proved once for the base-generic
sequence `baseZeroMultiplicity p n = 1 + ν_p(n)`; the dyadic statements
are its instances at `p = 2` through
`dyadicZeroMultiplicity_eq_baseZeroMultiplicity`.  The prefix law and
the Thue--Morse parity bridges are genuinely dyadic.

The main results are:

* `baseZeroMultiplicity_base_mul`, `baseZeroMultiplicity_base_pow_mul`
  and `baseZeroMultiplicity_ge_succ_iff_pow_dvd`, the base-generic
  recurrences and divisibility characterization;
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

/-! ## The base-generic multiplicity and its recurrences -/

/-- The totalized multiplicity `1 + ν_p(n)` at an arbitrary base `p`.
The dyadic sequence `dyadicZeroMultiplicity` is the instance `p = 2`
(`dyadicZeroMultiplicity_eq_baseZeroMultiplicity`).  The recurrences
below need only `1 < p`; multiplicativity needs `p` prime. -/
def baseZeroMultiplicity (p n : ℕ) : ℕ :=
  padicValNat p n + 1

/-- The totalized multiplicity is positive at every input. -/
theorem baseZeroMultiplicity_pos (p n : ℕ) :
    1 ≤ baseZeroMultiplicity p n := by
  simp [baseZeroMultiplicity]

/-- The index `1` is a simple zero at every base. -/
@[simp] theorem baseZeroMultiplicity_one (p : ℕ) :
    baseZeroMultiplicity p 1 = 1 := by
  rw [baseZeroMultiplicity, padicValNat_one_right]

/-- An index not divisible by the base is a simple zero. -/
theorem baseZeroMultiplicity_eq_one_of_not_dvd {p n : ℕ} (h : ¬p ∣ n) :
    baseZeroMultiplicity p n = 1 := by
  rw [baseZeroMultiplicity, padicValNat.eq_zero_of_not_dvd h]

/-- Multiplying a positive index by the base raises its multiplicity by
one. -/
theorem baseZeroMultiplicity_base_mul {p : ℕ} (hp : 1 < p) (n : ℕ)
    (hn : 1 ≤ n) :
    baseZeroMultiplicity p (p * n) = baseZeroMultiplicity p n + 1 := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp only [baseZeroMultiplicity, padicValNat_base_mul hp hn0]

/-- An index with a nonzero remainder modulo the base is a simple zero. -/
theorem baseZeroMultiplicity_base_mul_add {p : ℕ} (n : ℕ) {r : ℕ}
    (hr0 : 0 < r) (hrp : r < p) :
    baseZeroMultiplicity p (p * n + r) = 1 := by
  apply baseZeroMultiplicity_eq_one_of_not_dvd
  intro h
  have := Nat.le_of_dvd hr0 ((Nat.dvd_add_right (dvd_mul_right p n)).mp h)
  omega

/-- Extracting `r` factors of the base from a positive index raises its
multiplicity by exactly `r`. -/
theorem baseZeroMultiplicity_base_pow_mul {p : ℕ} (hp : 1 < p)
    (r n : ℕ) (hn : 1 ≤ n) :
    baseZeroMultiplicity p (p ^ r * n) =
      baseZeroMultiplicity p n + r := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp only [baseZeroMultiplicity, padicValNat_base_pow_mul hp hn0 r]
  omega

/-- A power of the base has multiplicity one more than its exponent. -/
theorem baseZeroMultiplicity_base_pow {p : ℕ} (hp : 1 < p) (r : ℕ) :
    baseZeroMultiplicity p (p ^ r) = r + 1 := by
  simp [baseZeroMultiplicity, padicValNat_base_pow hp]

/-- A positive index has multiplicity at least `r + 1` exactly when it is
divisible by `p ^ r`.  This zero-based form avoids truncated subtraction
in both the statement and its counting consequences. -/
theorem baseZeroMultiplicity_ge_succ_iff_pow_dvd {p : ℕ} (hp : 1 < p)
    (n r : ℕ) (hn : 1 ≤ n) :
    r + 1 ≤ baseZeroMultiplicity p n ↔ p ^ r ∣ n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hval := padicValNat_dvd_iff_le_of_ne_one
    (p := p) (by omega) (a := n) (n := r) hn0
  rw [baseZeroMultiplicity]
  constructor
  · intro h
    exact hval.mpr (by omega)
  · intro h
    have := hval.mp h
    omega

/-- A positive index has multiplicity exactly `r + 1` precisely when
`p ^ r`, but not `p ^ (r + 1)`, divides it. -/
theorem baseZeroMultiplicity_eq_succ_iff {p : ℕ} (hp : 1 < p)
    (n r : ℕ) (hn : 1 ≤ n) :
    baseZeroMultiplicity p n = r + 1 ↔
      p ^ r ∣ n ∧ ¬p ^ (r + 1) ∣ n := by
  constructor
  · intro h
    constructor
    · exact (baseZeroMultiplicity_ge_succ_iff_pow_dvd hp n r hn).mp
        (by omega)
    · intro hnext
      have := (baseZeroMultiplicity_ge_succ_iff_pow_dvd
        hp n (r + 1) hn).mpr hnext
      omega
  · rintro ⟨hr, hnext⟩
    have hlo :=
      (baseZeroMultiplicity_ge_succ_iff_pow_dvd hp n r hn).mpr hr
    have hnhi : ¬((r + 1) + 1 ≤ baseZeroMultiplicity p n) := by
      intro hhi
      exact hnext ((baseZeroMultiplicity_ge_succ_iff_pow_dvd
        hp n (r + 1) hn).mp hhi)
    omega

/-! ## Definition and dyadic recurrences -/

/-- The arithmetic multiplicity `1 + ν₂(n)` attached to a positive
integer zero.  The value at `0` is only the totalization of this formula;
the zero-multiplicity API below uses positive arguments. -/
def dyadicZeroMultiplicity (n : ℕ) : ℕ :=
  padicValNat 2 n + 1

/-- The dyadic multiplicity is the base-generic multiplicity at base
two; every dyadic recurrence below is the corresponding generic
statement at `p = 2`. -/
theorem dyadicZeroMultiplicity_eq_baseZeroMultiplicity :
    dyadicZeroMultiplicity = baseZeroMultiplicity 2 :=
  rfl

/-- The totalized arithmetic multiplicity is positive at every natural input.
For `n > 0`, this is the positivity of the corresponding dyadic zero order. -/
theorem dyadicZeroMultiplicity_pos (n : ℕ) :
    1 ≤ dyadicZeroMultiplicity n :=
  baseZeroMultiplicity_pos 2 n

/-- The first positive zero is simple. -/
@[simp] theorem dyadicZeroMultiplicity_one :
    dyadicZeroMultiplicity 1 = 1 :=
  baseZeroMultiplicity_one 2

/-- Doubling a positive index raises its dyadic zero multiplicity by one. -/
theorem dyadicZeroMultiplicity_two_mul (n : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity (2 * n) = dyadicZeroMultiplicity n + 1 :=
  baseZeroMultiplicity_base_mul Nat.one_lt_two n hn

/-- Every positive odd index is a simple zero. -/
@[simp] theorem dyadicZeroMultiplicity_two_mul_add_one (n : ℕ) :
    dyadicZeroMultiplicity (2 * n + 1) = 1 :=
  baseZeroMultiplicity_base_mul_add (p := 2) n Nat.one_pos Nat.one_lt_two

/-- Extracting `r` factors of two from a positive index raises its zero
multiplicity by exactly `r`. -/
theorem dyadicZeroMultiplicity_two_pow_mul (r n : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity (2 ^ r * n) = dyadicZeroMultiplicity n + r :=
  baseZeroMultiplicity_base_pow_mul Nat.one_lt_two r n hn

/-- A power of two has multiplicity one more than its exponent. -/
@[simp] theorem dyadicZeroMultiplicity_two_pow (r : ℕ) :
    dyadicZeroMultiplicity (2 ^ r) = r + 1 :=
  baseZeroMultiplicity_base_pow Nat.one_lt_two r

/-- A positive index has multiplicity at least `r + 1` exactly when it is
divisible by `2 ^ r`.  This zero-based form avoids truncated subtraction in
both the statement and its counting consequences. -/
theorem dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
    (n r : ℕ) (hn : 1 ≤ n) :
    r + 1 ≤ dyadicZeroMultiplicity n ↔ 2 ^ r ∣ n :=
  baseZeroMultiplicity_ge_succ_iff_pow_dvd Nat.one_lt_two n r hn

/-- A positive index has multiplicity exactly `r + 1` precisely when
`2 ^ r`, but not `2 ^ (r + 1)`, divides it. -/
theorem dyadicZeroMultiplicity_eq_succ_iff
    (n r : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity n = r + 1 ↔
      2 ^ r ∣ n ∧ ¬2 ^ (r + 1) ∣ n :=
  baseZeroMultiplicity_eq_succ_iff Nat.one_lt_two n r hn

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

/-- Among `1, …, N`, exactly `⌊N / p^r⌋` indices have base-`p`
multiplicity at least `r + 1`. -/
theorem card_baseZeroMultiplicity_ge_succ {p : ℕ} (hp : 1 < p)
    (N r : ℕ) :
    ((range N).filter
      (fun k => r + 1 ≤ baseZeroMultiplicity p (k + 1))).card =
        N / p ^ r := by
  rw [← Nat.card_multiples N (p ^ r)]
  apply congrArg Finset.card
  ext k
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hk, hmult⟩
    exact ⟨hk, (baseZeroMultiplicity_ge_succ_iff_pow_dvd hp
      (k + 1) r (by omega)).mp hmult⟩
  · rintro ⟨hk, hdvd⟩
    exact ⟨hk, (baseZeroMultiplicity_ge_succ_iff_pow_dvd hp
      (k + 1) r (by omega)).mpr hdvd⟩

/-- Among `1, …, N`, the number of indices of exact base-`p`
multiplicity `r + 1` is `⌊N / p^r⌋ - ⌊N / p^(r+1)⌋`. -/
theorem card_baseZeroMultiplicity_eq_succ {p : ℕ} (hp : 1 < p)
    (N r : ℕ) :
    ((range N).filter
      (fun k => baseZeroMultiplicity p (k + 1) = r + 1)).card =
        N / p ^ r - N / p ^ (r + 1) := by
  let lower := (range N).filter
    (fun k => r + 1 ≤ baseZeroMultiplicity p (k + 1))
  let higher := (range N).filter
    (fun k => (r + 1) + 1 ≤ baseZeroMultiplicity p (k + 1))
  have hsubset : higher ⊆ lower := by
    intro k hk
    simp only [higher, lower, mem_filter] at hk ⊢
    exact ⟨hk.1, by omega⟩
  have hexact :
      (range N).filter
          (fun k => baseZeroMultiplicity p (k + 1) = r + 1) =
        lower \ higher := by
    ext k
    simp only [lower, higher, mem_filter, mem_sdiff, mem_range]
    omega
  rw [hexact, card_sdiff_of_subset hsubset]
  change lower.card - higher.card = _
  rw [show lower.card = N / p ^ r by
      exact card_baseZeroMultiplicity_ge_succ hp N r,
    show higher.card = N / p ^ (r + 1) by
      exact card_baseZeroMultiplicity_ge_succ hp N (r + 1)]

/-- Among `1, …, N`, exactly `⌊N / 2^r⌋` indices have dyadic zero
multiplicity at least `r + 1`. -/
theorem card_dyadicZeroMultiplicity_ge_succ (N r : ℕ) :
    ((range N).filter
      (fun k => r + 1 ≤ dyadicZeroMultiplicity (k + 1))).card =
        N / 2 ^ r :=
  card_baseZeroMultiplicity_ge_succ Nat.one_lt_two N r

/-- Among `1, …, N`, the number of indices of exact dyadic zero
multiplicity `r + 1` is
`⌊N / 2^r⌋ - ⌊N / 2^(r+1)⌋`. -/
theorem card_dyadicZeroMultiplicity_eq_succ (N r : ℕ) :
    ((range N).filter
      (fun k => dyadicZeroMultiplicity (k + 1) = r + 1)).card =
        N / 2 ^ r - N / 2 ^ (r + 1) :=
  card_baseZeroMultiplicity_eq_succ Nat.one_lt_two N r

/-! ## Multiplicativity -/

/-- At a prime base the multiplicity sequence is multiplicative on
positive coprime inputs.  Coprimality ensures that at most one input has
a nonzero `p`-adic valuation, converting additivity of valuations into
multiplication of `1 + ν_p`. -/
theorem baseZeroMultiplicity_mul_of_coprime {p : ℕ} [hp : Fact p.Prime]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : m.Coprime n) :
    baseZeroMultiplicity p (m * n) =
      baseZeroMultiplicity p m * baseZeroMultiplicity p n := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hzero : padicValNat p m = 0 ∨ padicValNat p n = 0 := by
    by_cases hdvd : p ∣ m
    · right
      apply padicValNat.eq_zero_of_not_dvd
      intro hdvd'
      have hgcd : p ∣ Nat.gcd m n := Nat.dvd_gcd hdvd hdvd'
      rw [hcop.gcd_eq_one] at hgcd
      exact hp.out.ne_one (Nat.dvd_one.mp hgcd)
    · exact Or.inl (padicValNat.eq_zero_of_not_dvd hdvd)
  rcases hzero with hzero | hzero <;>
    simp [baseZeroMultiplicity, padicValNat.mul hm0 hn0, hzero]

/-- The dyadic zero-multiplicity sequence is multiplicative on positive
coprime inputs.  Coprimality ensures that at most one input has a nonzero
two-adic valuation, converting additivity of valuations into multiplication
of `1 + ν₂`. -/
theorem dyadicZeroMultiplicity_mul_of_coprime
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : m.Coprime n) :
    dyadicZeroMultiplicity (m * n) =
      dyadicZeroMultiplicity m * dyadicZeroMultiplicity n :=
  baseZeroMultiplicity_mul_of_coprime (p := 2) m n hm hn hcop

end Fabius
