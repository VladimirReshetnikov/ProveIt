import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum

/-!
# The base-`q` digit product

This file proves the atlas's generalized digit product `p1:thm:base-q-product`:
for `q ≥ 2`, a `q`-th root of unity `ζ`, and `u_n = ζ ^ s_q(n)` with `s_q` the
base-`q` digit sum,

`∑_{n < q^m} u_n z^n = ∏_{j < m} (∑_{r < q} ζ^r z^{r q^j})`,

together with the recursion `u_{qn+r} = ζ^r u_n` for `r < q`, and the
degree-zero Prouhet cancellation `∑_{n < q^m} u_n = 0` for `m ≥ 1`.

## Generality

The product identity has nothing to do with roots of unity.  It holds for an
**arbitrary digit weight** `w : ℕ → R` over any commutative semiring: writing
`d_j(n) = ⌊n / q^j⌋ mod q` for the `j`-th base-`q` digit,

`∑_{n < q^m} (∏_{j < m} w(d_j n)) z^n = ∏_{j < m} (∑_{r < q} w(r) z^{r q^j})`.

That is `sum_windowWeight_mul_pow`, and it needs no hypothesis on `w` or `ζ`
at all — not even `ζ^q = 1`.  The window form `∏_{j<m} w(d_j n)` is used
rather than a product over `Nat.digits` precisely so that no normalisation
`w 0 = 1` is needed: a window of fixed width `m` sees the leading zeros and
weights them by `w 0`, and both sides agree on that convention.  Specialising
to `w r = ζ^r` recovers `ζ ^ s_q(n)` because `ζ^0 = 1` makes leading zeros
invisible (`sum_digitAt_eq_digits_sum`).

The only place a root of unity enters is the vanishing of the factors at
`z = 1`, which is the hypothesis `∑_{r<q} ζ^r = 0`; in an integral domain that
follows from `ζ^q = 1`, `ζ ≠ 1` (`geom_sum_eq_zero_of_pow_eq_one`).

## Main declarations

* `digitAt q n j` — the `j`-th base-`q` digit `n / q^j % q`.
* `windowWeight w q m n` — the multiplicative digit weight over a window of
  width `m`.
* `sum_range_mul_eq_sum_sum` — the range decomposition
  `∑_{n < N s} f n = ∑_{r<s} ∑_{a<N} f (N r + a)`.
* `sum_windowWeight_mul_pow` — **the digit product at arbitrary weight**.
* `sum_digitAt_eq_digits_sum` — a window wide enough to hold `n` sums its
  digits to `(Nat.digits q n).sum`.
* `sum_zeta_pow_digits_sum_mul_pow` — **the atlas's `p1:eq:base-q-product`**.
* `digits_sum_mul_add`, `zeta_pow_digits_sum_mul_add` — the recursion
  `p1:eq:base-q-recursion`, `u_{qn+r} = ζ^r u_n`.
* `sum_zeta_pow_digits_sum_eq_zero` — degree-zero Prouhet cancellation.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-! ## Digits and digit windows -/

/-- The `j`-th base-`q` digit of `n`: `⌊n / q^j⌋ mod q`. -/
def digitAt (q n j : ℕ) : ℕ := n / q ^ j % q

/-- The multiplicative weight of the base-`q` digits of `n` in a window of
width `m`: `∏_{j < m} w (d_j n)`.  Leading zeros inside the window are
weighted by `w 0`. -/
def windowWeight {R : Type*} [CommSemiring R] (w : ℕ → R) (q m n : ℕ) : R :=
  ∏ j ∈ range m, w (digitAt q n j)

@[simp] theorem digitAt_zero (q n : ℕ) : digitAt q n 0 = n % q := by
  simp [digitAt]

theorem digitAt_succ (q n j : ℕ) : digitAt q n (j + 1) = digitAt q (n / q) j := by
  unfold digitAt
  rw [pow_succ', ← Nat.div_div_eq_div_mul]

/-- Adding a multiple of `q^m` does not change the digits below position `m`. -/
theorem digitAt_pow_mul_add_of_lt {q : ℕ} (hq : 0 < q) {j m : ℕ} (hj : j < m) (r a : ℕ) :
    digitAt q (q ^ m * r + a) j = digitAt q a j := by
  obtain ⟨k, rfl⟩ : ∃ k, m = j + k + 1 := ⟨m - j - 1, by omega⟩
  have hpos : 0 < q ^ j := pow_pos hq j
  have h : q ^ (j + k + 1) * r + a = a + q ^ j * (q * (q ^ k * r)) := by ring
  unfold digitAt
  rw [h, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

/-- The digit at position `m` of `q^m r + a` is `r`, when `a < q^m` and `r < q`. -/
theorem digitAt_pow_mul_add_self {q : ℕ} (hq : 1 < q) {m a r : ℕ} (ha : a < q ^ m)
    (hr : r < q) : digitAt q (q ^ m * r + a) m = r := by
  unfold digitAt
  have hpos : 0 < q ^ m := pow_pos (by omega) m
  rw [show q ^ m * r + a = a + q ^ m * r by ring, Nat.add_mul_div_left _ _ hpos,
    Nat.div_eq_of_lt ha, zero_add, Nat.mod_eq_of_lt hr]

/-- Appending a top digit multiplies the window weight by its weight. -/
theorem windowWeight_succ {R : Type*} [CommSemiring R] (w : ℕ → R) {q : ℕ} (hq : 1 < q)
    {m a r : ℕ} (ha : a < q ^ m) (hr : r < q) :
    windowWeight w q (m + 1) (q ^ m * r + a) = windowWeight w q m a * w r := by
  unfold windowWeight
  rw [prod_range_succ, digitAt_pow_mul_add_self hq ha hr]
  congr 1
  exact prod_congr rfl fun j hj => by
    rw [digitAt_pow_mul_add_of_lt (by omega) (mem_range.mp hj)]

/-! ## The range decomposition -/

/-- `∑_{n < N s} f n = ∑_{r < s} ∑_{a < N} f (N r + a)`: a block of length
`N s` is `s` consecutive blocks of length `N`. -/
theorem sum_range_mul_eq_sum_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N s : ℕ) :
    ∑ n ∈ range (N * s), f n = ∑ r ∈ range s, ∑ a ∈ range N, f (N * r + a) := by
  induction s with
  | zero => simp
  | succ s ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-! ## The digit product at arbitrary weight -/

/-- **The base-`q` digit product, at arbitrary digit weight.**  For every
`w : ℕ → R` and every `z`,

`∑_{n < q^m} (∏_{j<m} w (d_j n)) z^n = ∏_{j < m} ∑_{r < q} w r · z^{r q^j}`.

Choosing one digit independently at each of the `m` positions enumerates
`range (q^m)` exactly once; the exponent is the assembled integer and the
coefficient the product of the chosen digit weights. -/
theorem sum_windowWeight_mul_pow {R : Type*} [CommSemiring R] {q : ℕ} (hq : 1 < q)
    (w : ℕ → R) (z : R) (m : ℕ) :
    ∑ n ∈ range (q ^ m), windowWeight w q m n * z ^ n
      = ∏ j ∈ range m, ∑ r ∈ range q, w r * z ^ (r * q ^ j) := by
  induction m with
  | zero => simp [windowWeight]
  | succ m ih =>
      rw [pow_succ, sum_range_mul_eq_sum_sum, prod_range_succ, ← ih, sum_mul_sum, sum_comm]
      refine sum_congr rfl fun a ha => sum_congr rfl fun r hr => ?_
      rw [windowWeight_succ w hq (mem_range.mp ha) (mem_range.mp hr)]
      ring

/-! ## Digit sums -/

/-- A window wide enough to hold `n` sums its digits to the digit sum of
`Nat.digits`. -/
theorem sum_digitAt_eq_digits_sum {q : ℕ} (hq : 1 < q) (m : ℕ) :
    ∀ n, n < q ^ m → ∑ j ∈ range m, digitAt q n j = (Nat.digits q n).sum := by
  induction m with
  | zero =>
      intro n hn
      have h0 : n = 0 := by simpa using hn
      subst h0
      simp
  | succ m ih =>
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [digitAt]
      · rw [Nat.digits_def' hq hpos, List.sum_cons, sum_range_succ', digitAt_zero, add_comm]
        congr 1
        have hdiv : n / q < q ^ m :=
          (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [← pow_succ]; exact hn)
        rw [← ih (n / q) hdiv]
        exact sum_congr rfl fun j _ => digitAt_succ q n j

/-- The base-`q` digit sum of `q n + r` is `r` plus that of `n`, for `r < q`. -/
theorem digits_sum_mul_add {q : ℕ} (hq : 1 < q) (n r : ℕ) (hr : r < q) :
    (Nat.digits q (q * n + r)).sum = r + (Nat.digits q n).sum := by
  rcases Nat.eq_zero_or_pos (q * n + r) with h0 | hpos
  · have hr0 : r = 0 := by omega
    have hn0 : n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · have := Nat.mul_pos (by omega : 0 < q) h
        omega
    subst hr0
    subst hn0
    simp
  · have hxy : r ≠ 0 ∨ n ≠ 0 := by
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · right
        rintro rfl
        subst hr0
        simp at hpos
      · left
        omega
    rw [show q * n + r = r + q * n by ring, Nat.digits_add q hq r n hr hxy, List.sum_cons]

/-! ## The atlas's statements -/

/-- **The recursion `p1:eq:base-q-recursion`**: `u_{qn+r} = ζ^r u_n` for
`r < q`, where `u_n = ζ ^ s_q(n)`.  No hypothesis on `ζ`. -/
theorem zeta_pow_digits_sum_mul_add {R : Type*} [CommSemiring R] {q : ℕ} (hq : 1 < q)
    (ζ : R) (n r : ℕ) (hr : r < q) :
    ζ ^ (Nat.digits q (q * n + r)).sum = ζ ^ r * ζ ^ (Nat.digits q n).sum := by
  rw [digits_sum_mul_add hq n r hr, pow_add]

/-- **The generalized digit product `p1:eq:base-q-product`.**  For every
`ζ`, `z` in a commutative semiring — no root-of-unity hypothesis —

`∑_{n < q^m} ζ^{s_q(n)} z^n = ∏_{j < m} ∑_{r < q} ζ^r z^{r q^j}`. -/
theorem sum_zeta_pow_digits_sum_mul_pow {R : Type*} [CommSemiring R] {q : ℕ} (hq : 1 < q)
    (ζ z : R) (m : ℕ) :
    ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum * z ^ n
      = ∏ j ∈ range m, ∑ r ∈ range q, ζ ^ r * z ^ (r * q ^ j) := by
  rw [← sum_windowWeight_mul_pow hq (fun r => ζ ^ r) z m]
  refine sum_congr rfl fun n hn => ?_
  simp only [windowWeight]
  rw [prod_pow_eq_pow_sum, sum_digitAt_eq_digits_sum hq m n (mem_range.mp hn)]

/-- In an integral domain, a nontrivial `q`-th root of unity has vanishing
geometric sum: `1 + ζ + ⋯ + ζ^{q-1} = 0`. -/
theorem geom_sum_eq_zero_of_pow_eq_one {R : Type*} [CommRing R] [IsDomain R] {ζ : R}
    {q : ℕ} (h1 : ζ ^ q = 1) (hne : ζ ≠ 1) : ∑ r ∈ range q, ζ ^ r = 0 := by
  have h := mul_geom_sum ζ q
  rw [h1, sub_self] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hne
  · exact h0

/-- **Degree-zero Prouhet cancellation.**  If `∑_{r<q} ζ^r = 0` then every
complete block of `q^m` consecutive values of `ζ^{s_q(n)}`, `m ≥ 1`, sums to
zero: each factor of the digit product vanishes at `z = 1`. -/
theorem sum_zeta_pow_digits_sum_eq_zero {R : Type*} [CommSemiring R] {q : ℕ} (hq : 1 < q)
    {ζ : R} (hζ : ∑ r ∈ range q, ζ ^ r = 0) {m : ℕ} (hm : 0 < m) :
    ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum = 0 := by
  have h := sum_zeta_pow_digits_sum_mul_pow hq ζ (1 : R) m
  simp only [one_pow, mul_one] at h
  rw [h]
  exact prod_eq_zero (mem_range.mpr hm) hζ

end Fabius
