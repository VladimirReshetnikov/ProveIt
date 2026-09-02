import FabiusFunction.BaseDigitProduct
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Generalized Prouhet cancellation and the sharp moment in base `q`

This file proves the atlas's `p1:thm:base-q-Prouhet`.  With `q ≥ 2`,
`u_n = ζ ^ s_q(n)` for a nontrivial `q`-th root of unity `ζ`, and
`P_d(m) = ∑_{n < q^m} u_n n^d`:

* **Prouhet cancellation** `p1:eq:base-q-Prouhet`: `P_d(m) = 0` for `d < m`,
  and hence `∑_{n<q^m} u_n p(n) = 0` for every polynomial `p` of degree
  below `m`;
* **the sharp moment** `p1:eq:base-q-sharp-moment`:
  `P_m(m) = m! q^{m(m+1)/2} / (ζ - 1)^m`.

## Generality

Cancellation is proved from the single hypothesis `∑_{r<q} ζ^r = 0` over any
commutative semiring; nothing about `ζ^q` is used.  The sharp moment is
proved division-free over any commutative ring as

`(ζ - 1)^m · P_m(m) = m! · q^{0 + 1 + ⋯ + m}`,

from `ζ^q = 1` and `∑_{r<q} ζ^r = 0`; the displayed form with `/(ζ-1)^m`
follows in a field with `ζ ≠ 1`, and the Gauss sum `0 + ⋯ + m = m(m+1)/2` is
supplied separately so the exponent can be read either way.

## Method

The one-step recursion `digitPowerSum_succ` comes from splitting
`range (q^{m+1})` into `q` blocks `q^m r + a` (`sum_range_mul_eq_sum_sum`),
where the digit sum adds `r` (`digits_sum_pow_mul_add`) and the binomial
theorem expands `(a + q^m r)^d`.  In that expansion every `P_i(m)` with
`i < d` vanishes by induction, so for `d ≤ m` only `i = d` survives and its
coefficient is `∑_r ζ^r = 0`; for `d = m + 1` the two survivors are `i = m`,
whose coefficient is `(m+1) q^m ∑_r r ζ^r`, and `i = m+1`, again killed by
`∑ ζ^r = 0`.  The weighted geometric sum `(ζ - 1) ∑_{r<q} r ζ^r = q` is the
telescoping identity `geom_sum_mul_weighted`, proved for every `ζ` and then
specialised.

## Main declarations

* `digitPowerSum ζ q m d` — `P_d(m)`.
* `digits_sum_pow_mul_add` — `s_q(q^m r + a) = r + s_q(a)` for `a < q^m`, `r < q`.
* `digitPowerSum_succ` — the one-step recursion.
* `digitPowerSum_eq_zero_of_lt` — **Prouhet cancellation, monomial form**.
* `sum_zeta_pow_digits_sum_mul_eval_eq_zero` — **polynomial form** `p1:eq:base-q-Prouhet`.
* `geom_sum_mul_weighted`, `sub_one_mul_sum_mul_pow` — the weighted geometric sum.
* `sub_one_pow_mul_digitPowerSum_self` — **the sharp moment, division-free**.
* `digitPowerSum_self_eq_div` — **`p1:eq:base-q-sharp-moment`** in a field.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-! ## Digit sums under a top digit -/

/-- Placing the digit `r` at position `m` above `a < q^m` adds `r` to the
base-`q` digit sum. -/
theorem digits_sum_pow_mul_add {q : ℕ} (hq : 1 < q) {m a r : ℕ} (ha : a < q ^ m) (hr : r < q) :
    (Nat.digits q (q ^ m * r + a)).sum = r + (Nat.digits q a).sum := by
  have hlt : q ^ m * r + a < q ^ (m + 1) := by
    calc q ^ m * r + a < q ^ m * r + q ^ m := by omega
      _ = q ^ m * (r + 1) := by ring
      _ ≤ q ^ m * q := Nat.mul_le_mul_left _ hr
      _ = q ^ (m + 1) := (pow_succ q m).symm
  rw [← sum_digitAt_eq_digits_sum hq (m + 1) _ hlt, ← sum_digitAt_eq_digits_sum hq m a ha,
    sum_range_succ, digitAt_pow_mul_add_self hq ha hr, add_comm _ r]
  congr 1
  exact sum_congr rfl fun j hj => digitAt_pow_mul_add_of_lt (by omega) (mem_range.mp hj) r a

/-! ## The digit power sums -/

/-- `P_d(m) = ∑_{n < q^m} ζ^{s_q(n)} n^d`. -/
def digitPowerSum {R : Type*} [CommSemiring R] (ζ : R) (q m d : ℕ) : R :=
  ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum * (n : R) ^ d

@[simp] theorem digitPowerSum_zero_zero {R : Type*} [CommSemiring R] (ζ : R) (q : ℕ) :
    digitPowerSum ζ q 0 0 = 1 := by
  simp [digitPowerSum]

/-- The one-step recursion: splitting `range (q^{m+1})` into `q` blocks and
expanding the binomial,

`P_d(m+1) = ∑_{r<q} ζ^r ∑_{i≤d} (q^m r)^{d-i} C(d,i) P_i(m)`. -/
theorem digitPowerSum_succ {R : Type*} [CommSemiring R] {q : ℕ} (hq : 1 < q) (ζ : R)
    (m d : ℕ) :
    digitPowerSum ζ q (m + 1) d
      = ∑ r ∈ range q, ζ ^ r *
          ∑ i ∈ range (d + 1), ((q : R) ^ m * r) ^ (d - i) * (d.choose i : R) *
            digitPowerSum ζ q m i := by
  unfold digitPowerSum
  rw [pow_succ, sum_range_mul_eq_sum_sum]
  refine sum_congr rfl fun r hr => ?_
  calc ∑ a ∈ range (q ^ m), ζ ^ (Nat.digits q (q ^ m * r + a)).sum * ((q ^ m * r + a : ℕ) : R) ^ d
      = ∑ a ∈ range (q ^ m), ∑ i ∈ range (d + 1),
          ζ ^ r * ((((q : R) ^ m * r) ^ (d - i) * (d.choose i : R)) *
            (ζ ^ (Nat.digits q a).sum * (a : R) ^ i)) := by
        refine sum_congr rfl fun a ha => ?_
        rw [digits_sum_pow_mul_add hq (mem_range.mp ha) (mem_range.mp hr), pow_add]
        push_cast
        rw [show ((q : R) ^ m * r + a) = a + (q : R) ^ m * r by ring, add_pow, mul_sum]
        refine sum_congr rfl fun i hi => ?_
        ring
    _ = ζ ^ r * ∑ i ∈ range (d + 1), ((q : R) ^ m * r) ^ (d - i) * (d.choose i : R) *
          ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum * (n : R) ^ i := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun i hi => ?_
        rw [← mul_sum, ← mul_sum]

/-- **Prouhet cancellation, monomial form** (`p1:eq:base-q-Prouhet` for
`p(n) = n^d`): if `∑_{r<q} ζ^r = 0` then `P_d(m) = 0` for every `d < m`. -/
theorem digitPowerSum_eq_zero_of_lt {R : Type*} [CommSemiring R] {q : ℕ} (hq : 1 < q)
    {ζ : R} (hζ : ∑ r ∈ range q, ζ ^ r = 0) :
    ∀ m d : ℕ, d < m → digitPowerSum ζ q m d = 0 := by
  intro m
  induction m with
  | zero => intro d hd; omega
  | succ m ih =>
      intro d hd
      have hinner : ∀ r ∈ range q,
          ∑ i ∈ range (d + 1), ((q : R) ^ m * r) ^ (d - i) * (d.choose i : R) *
              digitPowerSum ζ q m i
            = digitPowerSum ζ q m d := by
        intro r hr
        rw [sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
          one_mul, sum_eq_zero, zero_add]
        intro i hi
        rw [ih i (by have := mem_range.mp hi; omega), mul_zero]
      rw [digitPowerSum_succ hq, sum_congr rfl fun r hr => by rw [hinner r hr], ← sum_mul, hζ,
        zero_mul]

/-- **Prouhet cancellation, polynomial form** (`p1:eq:base-q-Prouhet`): a
complete block of `q^m` values of `ζ^{s_q(n)}` annihilates every polynomial
of degree below `m`. -/
theorem sum_zeta_pow_digits_sum_mul_eval_eq_zero {R : Type*} [CommSemiring R] {q : ℕ}
    (hq : 1 < q) {ζ : R} (hζ : ∑ r ∈ range q, ζ ^ r = 0) {m : ℕ} (p : Polynomial R)
    (hp : p.natDegree < m) :
    ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum * p.eval (n : R) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range' hp, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun i hi => ?_
  have h := digitPowerSum_eq_zero_of_lt hq hζ m i (mem_range.mp hi)
  unfold digitPowerSum at h
  calc ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum * (p.coeff i * (n : R) ^ i)
      = p.coeff i * ∑ n ∈ range (q ^ m), ζ ^ (Nat.digits q n).sum * (n : R) ^ i := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring
    _ = 0 := by rw [h, mul_zero]

/-! ## The weighted geometric sum -/

/-- The telescoping identity behind the derivative of the geometric sum, for
**every** `ζ`: `(ζ - 1) ∑_{r<q} r ζ^r = (q - 1) ζ^q + 1 - ∑_{r<q} ζ^r`. -/
theorem geom_sum_mul_weighted {R : Type*} [CommRing R] (ζ : R) (q : ℕ) :
    (ζ - 1) * ∑ r ∈ range q, (r : R) * ζ ^ r
      = ((q : R) - 1) * ζ ^ q + 1 - ∑ r ∈ range q, ζ ^ r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [sum_range_succ, sum_range_succ, mul_add]
      push_cast
      linear_combination ih

/-- At a nontrivial `q`-th root of unity, `(ζ - 1) ∑_{r<q} r ζ^r = q`: the
atlas's `p1:eq:root-unity-derivative` without the division. -/
theorem sub_one_mul_sum_mul_pow {R : Type*} [CommRing R] {ζ : R} {q : ℕ} (h1 : ζ ^ q = 1)
    (hζ : ∑ r ∈ range q, ζ ^ r = 0) :
    (ζ - 1) * ∑ r ∈ range q, (r : R) * ζ ^ r = q := by
  rw [geom_sum_mul_weighted, h1, hζ]
  ring

/-! ## The sharp moment -/

/-- **The sharp moment, division-free** (`p1:eq:base-q-sharp-moment`):

`(ζ - 1)^m · P_m(m) = m! · q^{0+1+⋯+m}`

for a nontrivial `q`-th root of unity `ζ` in any commutative ring. -/
theorem sub_one_pow_mul_digitPowerSum_self {R : Type*} [CommRing R] {q : ℕ} (hq : 1 < q)
    {ζ : R} (h1 : ζ ^ q = 1) (hζ : ∑ r ∈ range q, ζ ^ r = 0) (m : ℕ) :
    (ζ - 1) ^ m * digitPowerSum ζ q m m
      = (m.factorial : R) * (q : R) ^ (∑ i ∈ range (m + 1), i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      -- In the recursion at `d = m + 1`, only `i = m` survives with a
      -- nonzero coefficient; `i = m + 1` carries `∑ ζ^r = 0`.
      have hinner : ∀ r ∈ range q,
          ∑ i ∈ range (m + 1 + 1), ((q : R) ^ m * r) ^ (m + 1 - i) * ((m + 1).choose i : R) *
              digitPowerSum ζ q m i
            = (q : R) ^ m * r * (m + 1 : R) * digitPowerSum ζ q m m
              + digitPowerSum ζ q m (m + 1) := by
        intro r hr
        rw [sum_range_succ, sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one,
          one_mul, one_mul, Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right,
          sum_eq_zero, zero_add]
        · push_cast
          ring
        · intro i hi
          rw [digitPowerSum_eq_zero_of_lt hq hζ m i (mem_range.mp hi), mul_zero]
      have hrec : digitPowerSum ζ q (m + 1) (m + 1)
          = (m + 1 : R) * (q : R) ^ m * (∑ r ∈ range q, (r : R) * ζ ^ r) *
              digitPowerSum ζ q m m := by
        rw [digitPowerSum_succ hq, sum_congr rfl fun r hr => by rw [hinner r hr]]
        simp_rw [mul_add, sum_add_distrib, ← sum_mul, hζ, zero_mul, add_zero, sum_mul]
        rw [sum_mul]
        refine sum_congr rfl fun r _ => ?_
        ring
      rw [hrec, pow_succ, sum_range_succ, pow_add, Nat.factorial_succ]
      push_cast
      calc (ζ - 1) ^ m * (ζ - 1) *
            ((m + 1 : R) * (q : R) ^ m * (∑ r ∈ range q, (r : R) * ζ ^ r) *
              digitPowerSum ζ q m m)
          = ((ζ - 1) ^ m * digitPowerSum ζ q m m) * ((ζ - 1) * ∑ r ∈ range q, (r : R) * ζ ^ r)
              * ((m + 1 : R) * (q : R) ^ m) := by ring
        _ = ((m.factorial : R) * (q : R) ^ (∑ i ∈ range (m + 1), i)) * (q : R)
              * ((m + 1 : R) * (q : R) ^ m) := by
            rw [ih, sub_one_mul_sum_mul_pow h1 hζ]
        _ = (m + 1 : R) * (m.factorial : R) * ((q : R) ^ (∑ i ∈ range (m + 1), i) *
              (q : R) ^ (m + 1)) := by ring

/-- The Gauss sum in the exponent: `0 + 1 + ⋯ + m = m (m + 1) / 2`. -/
theorem sum_range_succ_id_eq (m : ℕ) : ∑ i ∈ range (m + 1), i = m * (m + 1) / 2 := by
  have h := Finset.sum_range_id_mul_two (m + 1)
  rw [Nat.add_sub_cancel] at h
  exact (Nat.div_eq_of_eq_mul_left two_pos (by rw [← h]; ring)).symm

/-- **`p1:eq:base-q-sharp-moment`** in a field: for a nontrivial `q`-th root
of unity `ζ`,

`∑_{n<q^m} ζ^{s_q(n)} n^m = m! q^{m(m+1)/2} / (ζ - 1)^m`. -/
theorem digitPowerSum_self_eq_div {K : Type*} [Field K] {q : ℕ} (hq : 1 < q) {ζ : K}
    (h1 : ζ ^ q = 1) (hne : ζ ≠ 1) (m : ℕ) :
    digitPowerSum ζ q m m = (m.factorial : K) * (q : K) ^ (m * (m + 1) / 2) / (ζ - 1) ^ m := by
  have hζ : ∑ r ∈ range q, ζ ^ r = 0 := geom_sum_eq_zero_of_pow_eq_one h1 hne
  have h := sub_one_pow_mul_digitPowerSum_self hq h1 hζ m
  rw [sum_range_succ_id_eq] at h
  have hne' : (ζ - 1) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
  rw [eq_div_iff hne', mul_comm]
  exact h

end Fabius
