import FabiusFunction.ThueMorseFormalProduct
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Restricted binary partitions: the Green inverse of the block

For `m : ℕ` let `p_m(N)` be the number of ways of writing `N` as a
sum of parts drawn from `{1, 2, 4, …, 2^(m-1)}`, that is, the number
of tuples `(k_0, …, k_{m-1})` of naturals with `∑_{j<m} 2^j k_j = N`.
Its generating function is `∏_{j<m} (1 - z^(2^j))⁻¹`, so the
truncated Thue–Morse block

`Θ_m(z) = ∏_{j<m} (1 - z^(2^j)) = ∑_{n<2^m} ε(n) z^n`

and the counts `p_m` are convolution inverses of one another: `p_m`
is the **Green function** (discrete resolvent) of the finite
difference operator with symbol `Θ_m`.

Here `p_m` is *defined* by peeling the largest scale — choosing the
multiplicity `k` of the part `2^(m-1)` and representing the rest with
the smaller parts (`binaryPartitionCount` below) — and the two
identities the peeling yields,

* `p_{m+1}(N) = p_m(N)` for `N < 2^m`, and
* `p_{m+1}(N) = p_{m+1}(N - 2^m) + p_m(N)` for `2^m ≤ N`,

are exactly the statement `(1 - X^(2^m)) · P_{m+1} = P_m` for the
generating series `P_m = ∑_N p_m(N) X^N`.  Telescoping over `m` gives
the inverse identity, and `PowerSeries.coeff_mul` turns it into the
finite convolution against the Thue–Morse sign word.

The truncation of the convolution range at `min (N+1) (2^m)` is not
cosmetic.  The block has degree `2^m - 1`, which caps the range at
`2^m`; the further cap at `N + 1` is forced because natural
subtraction would replace each missing term `p_m(N - r)`, `r > N`, by
the nonzero value `p_m(0) = 1`.

## Main declarations

* `binaryPartitionCount` — the restricted count `p_m(N)`, by
  largest-scale peeling; `binaryPartitionCount_succ_of_lt` and
  `binaryPartitionCount_succ_recurrence` are the two halves of the
  scale-`2^m` recurrence.
* `binaryPartitionSeries` — the generating series `P_m` in `ℤ⟦X⟧`.
* `one_sub_X_pow_two_pow_mul_binaryPartitionSeries` — the single-step
  identity `(1 - X^(2^m)) · P_{m+1} = P_m`.
* **`prod_one_sub_X_two_pow_mul_binaryPartitionSeries`** — the
  headline: `(∏_{j<m} (1 - X^(2^j))) · P_m = 1` in `ℤ⟦X⟧`, with
  `binaryPartitionSeries_mul_prod_one_sub_X_two_pow` and
  `isUnit_binaryPartitionSeries` its commuted and unit forms.
* `coeff_prod_one_sub_X_two_pow` — the block's coefficient word:
  `ε(n)` below `2^m` and `0` from `2^m` on.
* **`thueMorseSign_binaryPartitionCount_convolution`** — the finite
  Green identity
  `∑_{r < min (N+1) (2^m)} ε(r) · p_m(N - r) = [N = 0]`.
* `binaryPartitionCount_one`, `binaryPartitionCount_two` — the closed
  forms `p_1 ≡ 1` and `p_2(N) = ⌊N/2⌋ + 1`, independent checks of the
  recursion; `binaryPartitionCount_eq_of_lt_two_pow` says the
  restriction becomes invisible once `2^m` exceeds `N`.

## Scope

Only the inverse identity and its finite consequence are proved.  The
identification of `binaryPartitionCount` with the cardinality of an
explicit `Finset` of tuples is **not** formalized here, and neither
is any asymptotic or quasipolynomial statement about `p_m`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### The restricted counting function -/

/-- **The restricted binary partition count** `p_m(N)`, defined by
peeling the largest available scale: with no parts at all only
`N = 0` is representable, and a level-`(m+1)` representation is a
choice of the multiplicity `k ≤ ⌊N / 2^m⌋` of the part `2^m` together
with a level-`m` representation of the remainder.

Informally `p_m(N)` is the number of tuples `(k_0, …, k_{m-1})` of
naturals with `∑_{j<m} 2^j k_j = N`; that reading is the motivation
for the recursion, but it is not formalized in this module. -/
def binaryPartitionCount : ℕ → ℕ → ℕ
  | 0, N => if N = 0 then 1 else 0
  | m + 1, N =>
      ∑ k ∈ range (N / 2 ^ m + 1),
        binaryPartitionCount m (N - 2 ^ m * k)

/-- With no parts available, only zero is representable. -/
@[simp] theorem binaryPartitionCount_zero (N : ℕ) :
    binaryPartitionCount 0 N = if N = 0 then 1 else 0 := rfl

/-- The defining largest-scale peeling. -/
theorem binaryPartitionCount_succ (m N : ℕ) :
    binaryPartitionCount (m + 1) N =
      ∑ k ∈ range (N / 2 ^ m + 1),
        binaryPartitionCount m (N - 2 ^ m * k) := rfl

/-- Below the new scale the extra part is unusable, so the count is
unchanged: `p_{m+1}(N) = p_m(N)` for `N < 2^m`. -/
theorem binaryPartitionCount_succ_of_lt (m N : ℕ) (h : N < 2 ^ m) :
    binaryPartitionCount (m + 1) N = binaryPartitionCount m N := by
  rw [binaryPartitionCount_succ, Nat.div_eq_of_lt h]
  simp

/-- **The scale-`2^m` recurrence**: for `2^m ≤ N`,
`p_{m+1}(N) = p_{m+1}(N - 2^m) + p_m(N)`.  Splitting on whether the
part `2^m` is used at all is the coefficient form of multiplication
by `1 - X^(2^m)`. -/
theorem binaryPartitionCount_succ_recurrence (m N : ℕ)
    (h : 2 ^ m ≤ N) :
    binaryPartitionCount (m + 1) N =
      binaryPartitionCount (m + 1) (N - 2 ^ m) +
        binaryPartitionCount m N := by
  have hd : 0 < 2 ^ m := Nat.two_pow_pos m
  have hdiv : (N - 2 ^ m) / 2 ^ m + 1 = N / 2 ^ m :=
    (Nat.div_eq_sub_div hd h).symm
  have hstep : ∀ k : ℕ,
      N - 2 ^ m * (k + 1) = N - 2 ^ m - 2 ^ m * k := by
    intro k
    rw [show 2 ^ m * (k + 1) = 2 ^ m + 2 ^ m * k from by ring,
      ← Nat.sub_sub]
  have hsum : ∑ k ∈ range (N / 2 ^ m),
      binaryPartitionCount m (N - 2 ^ m * (k + 1)) =
      ∑ k ∈ range (N / 2 ^ m),
        binaryPartitionCount m (N - 2 ^ m - 2 ^ m * k) :=
    Finset.sum_congr rfl fun k _ => by rw [hstep k]
  rw [binaryPartitionCount_succ m N,
    binaryPartitionCount_succ m (N - 2 ^ m), hdiv,
    Finset.sum_range_succ']
  simp only [mul_zero, Nat.sub_zero]
  rw [hsum]

/-- Zero has exactly one representation at every level: the empty
one. -/
@[simp] theorem binaryPartitionCount_zero_right (m : ℕ) :
    binaryPartitionCount m 0 = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [binaryPartitionCount_succ_of_lt m 0 (Nat.two_pow_pos m), ih]

/-- **Unary parts**: with only the part `1` available every `N` has a
single representation, `p_1 ≡ 1`. -/
theorem binaryPartitionCount_one (N : ℕ) :
    binaryPartitionCount 1 N = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h : (2 : ℕ) ^ 0 ≤ N + 1 := by rw [pow_zero]; omega
      have key := binaryPartitionCount_succ_recurrence 0 (N + 1) h
      rw [pow_zero, show N + 1 - 1 = N from by omega] at key
      have key2 : binaryPartitionCount 1 (N + 1) =
          binaryPartitionCount 1 N +
            binaryPartitionCount 0 (N + 1) := key
      rw [key2, ih, binaryPartitionCount_zero, if_neg (by omega)]

/-- The two-scale step, isolated so that the numeral `2` and the term
`1 + 1` never have to be matched syntactically. -/
private theorem binaryPartitionCount_two_add_two (N : ℕ) :
    binaryPartitionCount 2 (N + 2) =
      binaryPartitionCount 2 N + 1 := by
  have h : (2 : ℕ) ^ 1 ≤ N + 2 := by rw [pow_one]; omega
  have key := binaryPartitionCount_succ_recurrence 1 (N + 2) h
  rw [pow_one, show N + 2 - 2 = N from by omega,
    binaryPartitionCount_one] at key
  exact key

/-- **Parts `1` and `2`**: `p_2(N) = ⌊N/2⌋ + 1`, the number of
admissible multiplicities of the part `2`.  An independent check of
the recursion against a closed form. -/
theorem binaryPartitionCount_two (N : ℕ) :
    binaryPartitionCount 2 N = N / 2 + 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      by_cases h : 2 ≤ N
      · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
        rw [binaryPartitionCount_two_add_two, ih M (by omega)]
        omega
      · have hlt : N < 2 ^ 1 := by rw [pow_one]; omega
        have key := binaryPartitionCount_succ_of_lt 1 N hlt
        rw [binaryPartitionCount_one] at key
        rw [show N / 2 = 0 from by omega]
        simpa using key

/-- **The restriction is invisible below `2^m`**: once the smallest
omitted part exceeds `N`, enlarging the set of parts cannot change
the count. -/
theorem binaryPartitionCount_eq_of_lt_two_pow (m n N : ℕ)
    (hmn : m ≤ n) (hN : N < 2 ^ m) :
    binaryPartitionCount n N = binaryPartitionCount m N := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have h : N < 2 ^ n :=
        lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) hn)
      rw [binaryPartitionCount_succ_of_lt n N h, ih]

/-! ### The generating series and the inverse identity -/

/-- **The restricted binary partition series** `P_m = ∑_N p_m(N) X^N`
in `ℤ⟦X⟧`. -/
def binaryPartitionSeries (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun N => (binaryPartitionCount m N : ℤ)

/-- The coefficients of `P_m` are the restricted partition counts. -/
@[simp] theorem coeff_binaryPartitionSeries (m N : ℕ) :
    PowerSeries.coeff N (binaryPartitionSeries m) =
      (binaryPartitionCount m N : ℤ) := by
  simp [binaryPartitionSeries]

/-- With no parts available the generating series is `1`. -/
theorem binaryPartitionSeries_zero : binaryPartitionSeries 0 = 1 := by
  ext N
  rw [coeff_binaryPartitionSeries, PowerSeries.coeff_one,
    binaryPartitionCount_zero]
  by_cases h : N = 0 <;> simp [h]

/-- **One scale at a time**: `(1 - X^(2^m)) · P_{m+1} = P_m`.  This is
the pair `binaryPartitionCount_succ_of_lt` and
`binaryPartitionCount_succ_recurrence` read coefficientwise. -/
theorem one_sub_X_pow_two_pow_mul_binaryPartitionSeries (m : ℕ) :
    (1 - (X : PowerSeries ℤ) ^ 2 ^ m) *
        binaryPartitionSeries (m + 1) = binaryPartitionSeries m := by
  ext N
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_binaryPartitionSeries]
  by_cases h : 2 ^ m ≤ N
  · rw [if_pos h, binaryPartitionCount_succ_recurrence m N h]
    push_cast
    ring
  · rw [if_neg h, binaryPartitionCount_succ_of_lt m N (by omega)]
    ring

/-- **The Green inverse identity**: over `ℤ`, as formal power series,
`(∏_{j<m} (1 - X^(2^j))) · P_m = 1`.  The truncated Thue–Morse block
and the restricted binary partition counts are convolution inverses
of one another. -/
theorem prod_one_sub_X_two_pow_mul_binaryPartitionSeries (m : ℕ) :
    (∏ j ∈ range m, (1 - (X : PowerSeries ℤ) ^ 2 ^ j)) *
        binaryPartitionSeries m = 1 := by
  induction m with
  | zero => simpa using binaryPartitionSeries_zero
  | succ m ih =>
      rw [Finset.prod_range_succ, mul_assoc,
        one_sub_X_pow_two_pow_mul_binaryPartitionSeries m, ih]

/-- The commuted form of the inverse identity. -/
theorem binaryPartitionSeries_mul_prod_one_sub_X_two_pow (m : ℕ) :
    binaryPartitionSeries m *
        ∏ j ∈ range m, (1 - (X : PowerSeries ℤ) ^ 2 ^ j) = 1 := by
  rw [mul_comm]
  exact prod_one_sub_X_two_pow_mul_binaryPartitionSeries m

/-- The unit form: `P_m` is invertible in `ℤ⟦X⟧`, with the truncated
Thue–Morse block as its inverse. -/
theorem isUnit_binaryPartitionSeries (m : ℕ) :
    IsUnit (binaryPartitionSeries m) :=
  ⟨⟨binaryPartitionSeries m,
      ∏ j ∈ range m, (1 - (X : PowerSeries ℤ) ^ 2 ^ j),
      binaryPartitionSeries_mul_prod_one_sub_X_two_pow m,
      prod_one_sub_X_two_pow_mul_binaryPartitionSeries m⟩, rfl⟩

/-! ### The finite convolution -/

/-- Vanishing of the block polynomial above its degree.  A private
copy of `coeff_thueMorseBlockPolynomial_of_le` from
`FabiusFunction.ThueMorseBlockAlgebra`, repeated here only to keep
this module's import surface small. -/
private theorem coeff_block_of_le (r n : ℕ) (hn : 2 ^ r ≤ n) :
    (thueMorseBlockPolynomial r).coeff n = 0 := by
  rw [thueMorseBlockPolynomial, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkr : k < 2 ^ r := Finset.mem_range.mp hk
  rw [Polynomial.coeff_monomial, if_neg (by omega)]

/-- **The coefficient word of the truncated block**: the finite
product `∏_{j<m} (1 - X^(2^j))` carries the Thue–Morse sign `ε(n)` in
degree `n < 2^m` and vanishes from degree `2^m` on. -/
theorem coeff_prod_one_sub_X_two_pow (m n : ℕ) :
    PowerSeries.coeff n
        (∏ j ∈ range m, (1 - (X : PowerSeries ℤ) ^ 2 ^ j)) =
      if n < 2 ^ m then thueMorseSign n else 0 := by
  have hfold :
      (∏ j ∈ range m, (1 - (X : PowerSeries ℤ) ^ 2 ^ j)) =
        ((thueMorseBlockPolynomial m : Polynomial ℤ) :
          PowerSeries ℤ) := by
    rw [prod_range_one_sub_X_two_pow_eq_coe,
      thueMorseBlockPolynomial_eq_product]
    induction m with
    | zero => simp
    | succ k ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ, ih,
          ← Polynomial.coe_mul]
  rw [hfold, Polynomial.coeff_coe]
  by_cases h : n < 2 ^ m
  · rw [if_pos h, coeff_thueMorseBlockPolynomial m n h]
  · rw [if_neg h, coeff_block_of_le m n (by omega)]

/-- **The finite Green identity**: the Thue–Morse sign word convolved
against the restricted binary partition counts is the discrete delta,

`∑_{r < min (N+1) (2^m)} ε(r) · p_m(N - r) = [N = 0]`.

The upper limit `min (N+1) (2^m)` is `r ≤ min N (2^m - 1)`: the block
has degree `2^m - 1`, and the range may not be widened to
`Finset.range (2^m)`, because natural subtraction would replace the
missing terms `p_m(N - r)` with `r > N` by `p_m(0) = 1`. -/
theorem thueMorseSign_binaryPartitionCount_convolution (m N : ℕ) :
    ∑ r ∈ range (min (N + 1) (2 ^ m)),
        thueMorseSign r * (binaryPartitionCount m (N - r) : ℤ) =
      if N = 0 then 1 else 0 := by
  have key : ∑ r ∈ range (N + 1),
      (if r < 2 ^ m then thueMorseSign r else 0) *
        (binaryPartitionCount m (N - r) : ℤ) =
      (if N = 0 then (1 : ℤ) else 0) := by
    have h1 : PowerSeries.coeff N
        ((∏ j ∈ range m, (1 - (X : PowerSeries ℤ) ^ 2 ^ j)) *
          binaryPartitionSeries m) =
        PowerSeries.coeff N (1 : PowerSeries ℤ) := by
      rw [prod_one_sub_X_two_pow_mul_binaryPartitionSeries]
    rw [PowerSeries.coeff_one, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h1
    simpa only [coeff_prod_one_sub_X_two_pow,
      coeff_binaryPartitionSeries] using h1
  have hsub : range (min (N + 1) (2 ^ m)) ⊆ range (N + 1) :=
    Finset.range_subset_range.mpr (min_le_left _ _)
  have hzero : ∀ r ∈ range (N + 1),
      r ∉ range (min (N + 1) (2 ^ m)) →
      (if r < 2 ^ m then thueMorseSign r else 0) *
        (binaryPartitionCount m (N - r) : ℤ) = 0 := by
    intro r hr hr'
    have h1 := Finset.mem_range.mp hr
    have h2 : ¬ r < min (N + 1) (2 ^ m) := fun hc =>
      hr' (Finset.mem_range.mpr hc)
    have h3 : ¬ r < 2 ^ m := fun hlt => h2 (lt_min_iff.mpr ⟨h1, hlt⟩)
    rw [if_neg h3, zero_mul]
  have hbig : ∑ r ∈ range (min (N + 1) (2 ^ m)),
      (if r < 2 ^ m then thueMorseSign r else 0) *
        (binaryPartitionCount m (N - r) : ℤ) =
      ∑ r ∈ range (N + 1),
        (if r < 2 ^ m then thueMorseSign r else 0) *
          (binaryPartitionCount m (N - r) : ℤ) :=
    Finset.sum_subset hsub hzero
  rw [← key, ← hbig]
  exact Finset.sum_congr rfl fun r hr => by
    have hr' := Finset.mem_range.mp hr
    rw [if_pos (lt_min_iff.mp hr').2]

end Fabius
