import FabiusFunction.FabiusDiscreteLimitToeplitz
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# Condition number of a Fabius Toeplitz row at a general base

`FabiusDiscreteLimitToeplitz` fixes the base `q = 1 / 2` and proves
that the `n`-th Toeplitz row has total variation

`∑_{j≤n} |d(n,j)| = (-1/2; 1/2)_n / (1/2; 1/2)_n`.

This module carries that identity to an arbitrary base.  The row

`w_q(n,j) = (-1)^j [n,j]_q q^{C(j+1,2)} / (q;q)_n`

is the literal `q`-analogue of `Fabius.discreteLimitWeight`, built on
the denominator-free `Fabius.gaussianBinomial`, so the whole layer
runs on `Fabius.finite_qBinomial_theorem`, which holds over every
commutative ring and at every `q` and `z`.

Three tiers are separated deliberately, because they need different
hypotheses.

* The **signed** generating identity
  `∑_j w_q(n,j) z^j = (qz;q)_n / (q;q)_n` is a direct reading of the
  finite `q`-binomial theorem and needs **no hypothesis at all**: over
  a commutative ring in the numerator-only form, and over a field in
  the quotient form.
* The **sign pattern** `(-1)^j w_q(n,j) > 0` needs `0 < q < 1`.
* The **absolute-value** identity
  `∑_j |w_q(n,j)| = (-q;q)_n / (q;q)_n` needs `0 ≤ q < 1`.

The two order hypotheses are not decoration.  The bases `q = -1/2` and
`q = 2` both break the absolute-value identity already in row one, and
both failures are recorded here as theorems rather than as prose.

## Main declarations

* `qToeplitzNumerator` -- the denominator-free row entry, over any
  commutative ring.
* `sum_qToeplitzNumerator_mul_pow` -- **the general-`q` signed
  identity**, hypothesis-free over every commutative ring.
* `sum_qToeplitzNumerator_mul_pow_one` -- its `q = 1` shadow, the
  ordinary binomial theorem.
* `sum_gaussianBinomial_mul_pow` -- the unsigned companion sum, equal
  to `(-q;q)_n`; also hypothesis-free.
* `qToeplitzWeight` -- the normalized row entry over a field, with
  `qToeplitzWeight_one_left` and `qToeplitzWeight_one_right` giving
  row one in closed form.
* `sum_qToeplitzWeight_mul_pow` -- the quotient form of the signed
  identity, still with no hypothesis on `q` or `z`.
* `qToeplitzWeight_one` and `sum_qToeplitzWeight_one_ne_one` -- at
  `q = 1` every entry of a nonempty row is zero and the row mass is
  `0`, not `1`.
* `gaussianBinomial_pos` and `finiteQPochhammerIn_self_pos` -- the two
  positivity inputs, under `0 ≤ q` and under `0 ≤ q < 1`.
* `neg_one_pow_mul_qToeplitzWeight_pos` -- **exact sign alternation**
  for `0 < q < 1`.
* `abs_qToeplitzWeight` and `sum_abs_qToeplitzWeight` -- **the
  general-`q` condition-number identity** for `0 ≤ q < 1`.
* `one_le_sum_abs_qToeplitzWeight` -- the condition number is at least
  one.
* `sum_abs_qToeplitzWeight_ne_of_neg` and
  `sum_abs_qToeplitzWeight_ne_of_one_lt` -- guards showing that
  `0 ≤ q` and `q < 1` are both needed.
* `qToeplitzWeight_half`,
  `sum_range_discreteLimitWeight_mul_pow_of_qToeplitz` and
  `sum_abs_discreteLimitWeight_of_qToeplitz` -- the half-base
  specialization, re-deriving the two established `q = 1/2` theorems
  of `FabiusDiscreteLimitToeplitz` from the general ones.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-! ## The denominator-free row, over a commutative ring -/

/-- The numerator of the general-`q` Fabius Toeplitz weight,
`(-1)^j [n,j]_q q^{C(j+1,2)}`.  No division occurs, so it is defined
over every commutative ring and at every `q`. -/
def qToeplitzNumerator {R : Type*} [CommRing R]
    (q : R) (n j : ℕ) : R :=
  (-1 : R) ^ j * gaussianBinomial q n j * q ^ ((j + 1).choose 2)

/-- **The general-`q` signed row identity, denominator free.**  For
every commutative ring, every `q`, and every `z`,

`∑_{j≤n} (-1)^j [n,j]_q q^{C(j+1,2)} z^j = (q z; q)_n`.

This is `Fabius.finite_qBinomial_theorem` read at the argument `q z`.
It carries no hypothesis whatsoever, and it is the entire content of
the signed half of the condition-number question. -/
theorem sum_qToeplitzNumerator_mul_pow
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      qToeplitzNumerator q n j * z ^ j) =
      finiteQPochhammerIn (q * z) q n := by
  rw [← finite_qBinomial_theorem q (q * z) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (j + 1).choose 2 = j.choose 2 + j := choose_succ_two j
  rw [qToeplitzNumerator, hc, pow_add, mul_pow]
  ring

/-- **The `q = 1` shadow of the signed identity.**  At `q = 1` the
weight `q^{C(j+1,2)}` disappears and `[n,j]_q` becomes `C(n,j)`, so
the identity degenerates to the ordinary binomial theorem
`∑_{j≤n} (-1)^j C(n,j) z^j = (1-z)^n`. -/
theorem sum_qToeplitzNumerator_mul_pow_one
    {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      qToeplitzNumerator (1 : R) n j * z ^ j) = (1 - z) ^ n := by
  rw [sum_qToeplitzNumerator_mul_pow, one_mul,
    finiteQPochhammerIn_one]

private theorem qToeplitzNumerator_mul_neg_one_pow
    {R : Type*} [CommRing R] (q : R) (n j : ℕ) :
    qToeplitzNumerator q n j * (-1 : R) ^ j =
      gaussianBinomial q n j * q ^ ((j + 1).choose 2) := by
  have hs : (-1 : R) ^ j * (-1 : R) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [qToeplitzNumerator]
  calc
    (-1 : R) ^ j * gaussianBinomial q n j *
        q ^ ((j + 1).choose 2) * (-1 : R) ^ j =
        ((-1 : R) ^ j * (-1 : R) ^ j) *
          (gaussianBinomial q n j * q ^ ((j + 1).choose 2)) := by
      ring
    _ = gaussianBinomial q n j * q ^ ((j + 1).choose 2) := by
      rw [hs, one_mul]

/-- **The unsigned companion sum.**  Dropping the alternating sign
from the row numerator evaluates the finite `q`-binomial theorem at
`z = -q`:

`∑_{j≤n} [n,j]_q q^{C(j+1,2)} = (-q; q)_n`.

Like the signed identity this holds over every commutative ring with
no hypothesis.  Order hypotheses enter only when one wants the left
side to be a sum of absolute values. -/
theorem sum_gaussianBinomial_mul_pow
    {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      gaussianBinomial q n j * q ^ ((j + 1).choose 2)) =
      finiteQPochhammerIn (-q) q n := by
  have h := sum_qToeplitzNumerator_mul_pow q (-1 : R) n
  rw [show q * (-1 : R) = -q by ring] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ =>
    (qToeplitzNumerator_mul_neg_one_pow q n j).symm

/-! ## The normalized row, over a field -/

/-- The general-`q` Fabius Toeplitz weight.  At `q = 1 / 2` it is
`Fabius.discreteLimitWeight`; see `qToeplitzWeight_half`. -/
noncomputable def qToeplitzWeight {K : Type*} [Field K]
    (q : K) (n j : ℕ) : K :=
  (-1 : K) ^ j * gaussianBinomial q n j *
      q ^ ((j + 1).choose 2) /
    finiteQPochhammerIn q q n

/-- The weight is the denominator-free numerator over `(q;q)_n`. -/
theorem qToeplitzWeight_eq_div {K : Type*} [Field K]
    (q : K) (n j : ℕ) :
    qToeplitzWeight q n j =
      qToeplitzNumerator q n j / finiteQPochhammerIn q q n := by
  rw [qToeplitzWeight, qToeplitzNumerator]

/-- **The general-`q` signed generating identity.**  Over every field,
for every `q` and `z`,

`∑_{j≤n} w_q(n,j) z^j = (q z; q)_n / (q;q)_n`.

No hypothesis is imposed; `sum_qToeplitzWeight_one` records what the
statement says in the degenerate case `(q;q)_n = 0`. -/
theorem sum_qToeplitzWeight_mul_pow {K : Type*} [Field K]
    (q z : K) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), qToeplitzWeight q n j * z ^ j) =
      finiteQPochhammerIn (q * z) q n /
        finiteQPochhammerIn q q n := by
  rw [← sum_qToeplitzNumerator_mul_pow q z n, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qToeplitzWeight, qToeplitzNumerator]
  ring

/-- Closed form of the first entry of row one, over any field. -/
theorem qToeplitzWeight_one_left {K : Type*} [Field K] (q : K) :
    qToeplitzWeight q 1 0 = 1 / (1 - q) := by
  have hc : ((0 : ℕ) + 1).choose 2 = 0 := by decide
  rw [qToeplitzWeight, hc, gaussianBinomial_zero_right,
    finiteQPochhammerIn, Finset.prod_range_one]
  simp only [pow_zero, one_mul, mul_one]

/-- Closed form of the second entry of row one, over any field. -/
theorem qToeplitzWeight_one_right {K : Type*} [Field K] (q : K) :
    qToeplitzWeight q 1 1 = -q / (1 - q) := by
  have hc : ((1 : ℕ) + 1).choose 2 = 1 := by decide
  rw [qToeplitzWeight, hc, gaussianBinomial_self,
    finiteQPochhammerIn, Finset.prod_range_one]
  simp only [pow_zero, pow_one, one_mul, mul_one, neg_mul]

/-! ## The degenerate base `q = 1` -/

/-- At `q = 1` the row denominator `(1;1)_{n+1}` vanishes, so every
entry of a nonempty row is zero.  The hypothesis `q < 1` used below is
therefore not cosmetic. -/
theorem qToeplitzWeight_one {K : Type*} [Field K] (n j : ℕ) :
    qToeplitzWeight (1 : K) (n + 1) j = 0 := by
  rw [qToeplitzWeight, finiteQPochhammerIn_one_left, div_zero]

/-- The `q = 1` row has mass zero. -/
theorem sum_qToeplitzWeight_one {K : Type*} [Field K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 2),
      qToeplitzWeight (1 : K) (n + 1) j) = 0 :=
  Finset.sum_eq_zero fun j _ => qToeplitzWeight_one n j

/-- **Guard on the row-mass theorem.**  At `q = 1` the mass of a
nonempty row is `0`, not `1`, so `sum_qToeplitzWeight` genuinely needs
a hypothesis forcing `(q;q)_n ≠ 0`. -/
theorem sum_qToeplitzWeight_one_ne_one {K : Type*} [Field K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 2),
      qToeplitzWeight (1 : K) (n + 1) j) ≠ 1 := by
  rw [sum_qToeplitzWeight_one]
  exact zero_ne_one

/-! ## Positivity inputs on an ordered field -/

/-- Gaussian coefficients are nonnegative at every nonnegative `q`,
including strictly above the diagonal, where they vanish. -/
theorem gaussianBinomial_nonneg
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq : 0 ≤ q) (n k : ℕ) :
    0 ≤ gaussianBinomial q n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simp
      | succ k => simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussianBinomial_succ_succ]
          exact add_nonneg (ih (k + 1))
            (mul_nonneg (pow_nonneg hq _) (ih k))

private theorem gaussianBinomial_pos_aux
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq : 0 ≤ q) :
    ∀ n k : ℕ, k ≤ n → 0 < gaussianBinomial q n k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := Nat.succ_le_succ_iff.mp hk
          by_cases hkn' : k = n
          · subst k
            simp
          · have hklt : k < n := lt_of_le_of_ne hkn hkn'
            have hk1n : k + 1 ≤ n := Nat.succ_le_iff.mpr hklt
            have h1 : 0 < gaussianBinomial q n (k + 1) :=
              ih (k + 1) hk1n
            have h2 : 0 ≤ q ^ (n - k) * gaussianBinomial q n k :=
              mul_nonneg (pow_nonneg hq _)
                (gaussianBinomial_nonneg hq n k)
            rw [gaussianBinomial_succ_succ]
            linarith

/-- **Gaussian coefficients are strictly positive in the admissible
range**, for every nonnegative `q`.  The hypothesis is only `0 ≤ q`;
strict positivity of the base is not needed: off the diagonal the
unweighted term of the `q`-Pascal recursion already carries the
positivity, and on the diagonal the coefficient is `1` because the
weight `q ^ (n - k)` has exponent zero there. -/
theorem gaussianBinomial_pos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq : 0 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    0 < gaussianBinomial q n k :=
  gaussianBinomial_pos_aux hq n k hk

/-- `(q;q)_n` is strictly positive for `0 ≤ q < 1`: each factor
`1 - q q^j` is positive because `q q^j ≤ q < 1`.  This is the
general-base counterpart of `Fabius.halfQPochhammer_pos`. -/
theorem finiteQPochhammerIn_self_pos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    0 < finiteQPochhammerIn q q n := by
  rw [finiteQPochhammerIn]
  refine Finset.prod_pos fun j _ => ?_
  have hpow : q ^ j ≤ 1 := pow_le_one₀ hq0 hq1.le
  have hmul : q * q ^ j ≤ q := mul_le_of_le_one_right hq0 hpow
  linarith

/-- `(-q;q)_n` is strictly positive for `0 ≤ q`: each factor is
`1 + q q^j`, and `q q^j` is nonnegative.  This is the numerator of the
condition-number identity below. -/
theorem finiteQPochhammerIn_neg_self_pos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 ≤ q) (n : ℕ) :
    0 < finiteQPochhammerIn (-q) q n := by
  rw [finiteQPochhammerIn]
  refine Finset.prod_pos fun j _ => ?_
  have hnn : (0 : K) ≤ q * q ^ j := mul_nonneg hq0 (pow_nonneg hq0 j)
  rw [neg_mul, sub_neg_eq_add]
  linarith

/-! ## Row mass, sign pattern, and the condition number -/

/-- **Every general-`q` row has mass one**, for `0 ≤ q < 1`.  This is
the value at `z = 1` of `sum_qToeplitzWeight_mul_pow`, the hypotheses
serving only to make `(q;q)_n` nonzero. -/
theorem sum_qToeplitzWeight
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), qToeplitzWeight q n j) = 1 := by
  have h := sum_qToeplitzWeight_mul_pow q 1 n
  simp only [one_pow, mul_one] at h
  rw [h]
  exact div_self (finiteQPochhammerIn_self_pos hq0 hq1 n).ne'

/-- **Exact sign alternation.**  For `0 < q < 1` the `j`-th entry of
row `n` has sign exactly `(-1)^j`.  This is what turns the sum of
absolute values into an evaluation of the `q`-binomial theorem at
`z = -q`.  Strict positivity of `q` is needed: at `q = 0` the entries
with `j ≥ 1` vanish, as `qToeplitzWeight_zero_one_right` records. -/
theorem neg_one_pow_mul_qToeplitzWeight_pos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 < q) (hq1 : q < 1) {n j : ℕ} (hj : j ≤ n) :
    0 < (-1 : K) ^ j * qToeplitzWeight q n j := by
  have hG : 0 < gaussianBinomial q n j :=
    gaussianBinomial_pos hq0.le hj
  have hD : 0 < finiteQPochhammerIn q q n :=
    finiteQPochhammerIn_self_pos hq0.le hq1 n
  have hqp : 0 < q ^ ((j + 1).choose 2) := pow_pos hq0 _
  have hsq : (-1 : K) ^ j * (-1 : K) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hkey :
      (-1 : K) ^ j * qToeplitzWeight q n j =
        ((-1 : K) ^ j * (-1 : K) ^ j) *
          (gaussianBinomial q n j * q ^ ((j + 1).choose 2)) /
            finiteQPochhammerIn q q n := by
    rw [qToeplitzWeight]
    ring
  rw [hkey, hsq, one_mul]
  exact div_pos (mul_pos hG hqp) hD

/-- **Guard on the strictness hypothesis.**  At `q = 0` the second
entry of row one is zero, so the alternation above is not strict
there.  The absolute-value identity below, which assumes only
`0 ≤ q`, still applies at `q = 0`. -/
theorem qToeplitzWeight_zero_one_right :
    qToeplitzWeight (0 : ℚ) 1 1 = 0 := by
  rw [qToeplitzWeight_one_right]
  norm_num

/-- Absolute value of a general-`q` Toeplitz entry inside its row.
For `0 ≤ q < 1` every factor surviving the removal of the alternating
sign is nonnegative, and the denominator is positive. -/
theorem abs_qToeplitzWeight
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) {n j : ℕ} (hj : j ≤ n) :
    |qToeplitzWeight q n j| =
      gaussianBinomial q n j * q ^ ((j + 1).choose 2) /
        finiteQPochhammerIn q q n := by
  have hG : 0 < gaussianBinomial q n j := gaussianBinomial_pos hq0 hj
  have hD : 0 < finiteQPochhammerIn q q n :=
    finiteQPochhammerIn_self_pos hq0 hq1 n
  have h1 : |(-1 : K) ^ j| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have hnum :
      |(-1 : K) ^ j * gaussianBinomial q n j *
          q ^ ((j + 1).choose 2)| =
        gaussianBinomial q n j * q ^ ((j + 1).choose 2) := by
    rw [abs_mul, abs_mul, h1, one_mul, abs_of_pos hG, abs_pow,
      abs_of_nonneg hq0]
  rw [qToeplitzWeight, abs_div, hnum, abs_of_pos hD]

/-- **The general-`q` condition-number identity.**  For `0 ≤ q < 1`
the total variation of the `n`-th general-`q` Fabius Toeplitz row is

`∑_{j≤n} |w_q(n,j)| = (-q; q)_n / (q; q)_n`.

At `q = 1/2` this is `Fabius.sum_abs_discreteLimitWeight`, re-derived
below as `sum_abs_discreteLimitWeight_of_qToeplitz`. -/
theorem sum_abs_qToeplitzWeight
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), |qToeplitzWeight q n j|) =
      finiteQPochhammerIn (-q) q n / finiteQPochhammerIn q q n := by
  calc
    (∑ j ∈ Finset.range (n + 1), |qToeplitzWeight q n j|) =
        ∑ j ∈ Finset.range (n + 1),
          gaussianBinomial q n j * q ^ ((j + 1).choose 2) /
            finiteQPochhammerIn q q n := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact abs_qToeplitzWeight hq0 hq1
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = finiteQPochhammerIn (-q) q n /
          finiteQPochhammerIn q q n := by
      rw [← Finset.sum_div, sum_gaussianBinomial_mul_pow]

/-- The condition number is never below one: a row of mass one cannot
have total variation smaller than one.  In particular the right-hand
side of the identity above never degenerates to zero. -/
theorem one_le_sum_abs_qToeplitzWeight
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    1 ≤ ∑ j ∈ Finset.range (n + 1), |qToeplitzWeight q n j| := by
  calc
    (1 : K) =
        |∑ j ∈ Finset.range (n + 1), qToeplitzWeight q n j| := by
      rw [sum_qToeplitzWeight hq0 hq1 n, abs_one]
    _ ≤ ∑ j ∈ Finset.range (n + 1), |qToeplitzWeight q n j| :=
      Finset.abs_sum_le_sum_abs _ _

/-! ## Both order hypotheses are necessary -/

/-- **Guard: the hypothesis `0 ≤ q` cannot be dropped.**  By the two
row-one closed forms, at `q = -1/2` both entries are positive, `2/3`
and `1/3`, so the alternation fails.  The total variation is then `1`
while `(-q;q)_1 / (q;q)_1 = 1/3`. -/
theorem sum_abs_qToeplitzWeight_ne_of_neg :
    (∑ j ∈ Finset.range 2, |qToeplitzWeight (-1 / 2 : ℚ) 1 j|) ≠
      finiteQPochhammerIn (-(-1 / 2) : ℚ) (-1 / 2) 1 /
        finiteQPochhammerIn (-1 / 2 : ℚ) (-1 / 2) 1 := by
  have h0 : qToeplitzWeight (-1 / 2 : ℚ) 1 0 = 2 / 3 := by
    rw [qToeplitzWeight_one_left]
    norm_num
  have h1 : qToeplitzWeight (-1 / 2 : ℚ) 1 1 = 1 / 3 := by
    rw [qToeplitzWeight_one_right]
    norm_num
  have hL : (∑ j ∈ Finset.range 2,
      |qToeplitzWeight (-1 / 2 : ℚ) 1 j|) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, h0, h1,
      abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2 / 3),
      abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 3)]
    norm_num
  have hR : finiteQPochhammerIn (-(-1 / 2) : ℚ) (-1 / 2) 1 /
      finiteQPochhammerIn (-1 / 2 : ℚ) (-1 / 2) 1 = 1 / 3 := by
    simp only [finiteQPochhammerIn, Finset.prod_range_one]
    norm_num
  rw [hL, hR]
  norm_num

/-- **Guard: the hypothesis `q < 1` cannot be dropped.**  At `q = 2`
the denominator `(q;q)_1 = -1` is negative, so the total variation `3`
disagrees with `(-q;q)_1 / (q;q)_1 = -3`. -/
theorem sum_abs_qToeplitzWeight_ne_of_one_lt :
    (∑ j ∈ Finset.range 2, |qToeplitzWeight (2 : ℚ) 1 j|) ≠
      finiteQPochhammerIn (-2 : ℚ) 2 1 /
        finiteQPochhammerIn (2 : ℚ) 2 1 := by
  have h0 : qToeplitzWeight (2 : ℚ) 1 0 = -1 := by
    rw [qToeplitzWeight_one_left]
    norm_num
  have h1 : qToeplitzWeight (2 : ℚ) 1 1 = 2 := by
    rw [qToeplitzWeight_one_right]
    norm_num
  have hL : (∑ j ∈ Finset.range 2,
      |qToeplitzWeight (2 : ℚ) 1 j|) = 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, h0, h1, abs_neg, abs_one,
      abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
    norm_num
  have hR : finiteQPochhammerIn (-2 : ℚ) 2 1 /
      finiteQPochhammerIn (2 : ℚ) 2 1 = -3 := by
    simp only [finiteQPochhammerIn, Finset.prod_range_one]
    norm_num
  rw [hL, hR]
  norm_num

/-! ## The half base, recovered -/

/-- **The general-`q` weight at `q = 1/2` is the established Fabius
Toeplitz weight.**  The two definitions agree termwise, so every
result above specializes to the half base with no translation lemma
beyond this one. -/
theorem qToeplitzWeight_half (n j : ℕ) :
    qToeplitzWeight (1 / 2 : ℚ) n j = discreteLimitWeight n j := by
  have hden : finiteQPochhammerIn (1 / 2 : ℚ) (1 / 2) n =
      halfQPochhammer n := rfl
  rw [qToeplitzWeight, discreteLimitWeight, hden,
    gaussianBinomial_half_eq_halfQBinomial]

/-- The half-base row generating polynomial, re-derived from the
general-`q` signed identity.  The statement is
`Fabius.sum_range_discreteLimitWeight_mul_pow`. -/
theorem sum_range_discreteLimitWeight_mul_pow_of_qToeplitz
    (n : ℕ) (z : ℚ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j * z ^ j) =
      finiteQPochhammer (z / 2) (1 / 2) n / halfQPochhammer n := by
  have h := sum_qToeplitzWeight_mul_pow (1 / 2 : ℚ) z n
  have hnum : finiteQPochhammerIn ((1 / 2 : ℚ) * z) (1 / 2) n =
      finiteQPochhammer (z / 2) (1 / 2) n := by
    rw [finiteQPochhammerIn_rat_eq,
      show (1 / 2 : ℚ) * z = z / 2 by ring]
  have hden : finiteQPochhammerIn (1 / 2 : ℚ) (1 / 2) n =
      halfQPochhammer n := rfl
  rw [hnum, hden] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [qToeplitzWeight_half]

/-- **The half-base condition number, re-derived.**  Specializing
`sum_abs_qToeplitzWeight` at `q = 1/2` reproves the statement of
`Fabius.sum_abs_discreteLimitWeight`.  This is the consistency check
between the general identity and the established one: had the general
statement been wrong, this specialization could not have been
closed. -/
theorem sum_abs_discreteLimitWeight_of_qToeplitz (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) =
      finiteQPochhammer (-1 / 2) (1 / 2) n / halfQPochhammer n := by
  have h := sum_abs_qToeplitzWeight (K := ℚ) (q := 1 / 2)
    (by norm_num) (by norm_num) n
  have hneg : (-(1 / 2) : ℚ) = -1 / 2 := by norm_num
  have hnum : finiteQPochhammerIn (-(1 / 2) : ℚ) (1 / 2) n =
      finiteQPochhammer (-1 / 2) (1 / 2) n := by
    rw [finiteQPochhammerIn_rat_eq, hneg]
  have hden : finiteQPochhammerIn (1 / 2 : ℚ) (1 / 2) n =
      halfQPochhammer n := rfl
  rw [hnum, hden] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [qToeplitzWeight_half]

end Fabius
