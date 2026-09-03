import FabiusFunction.QPochhammerElementaryIdentities
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The terminating very-well-poised `₆φ₅` summation

For `N : ℕ` and `q, a, b, c` in an arbitrary field this module proves

`∑_{k=0}^{N} (1 - a q^{2k})/(1 - a) · (a,b,c,q^{-N};q)_k / ((q, aq/b, aq/c, aq^{N+1};q)_k)
    · (a q^{N+1}/(bc))^k = (aq, aq/(bc);q)_N / ((aq/b, aq/c;q)_N)`,

where `q^{-N}` is written `(q ^ N)⁻¹`, the house convention already fixed by
`Fabius.q_pfaff_saalschutz`.  This is `qg:cor-jackson-6phi5`
(equation `qg:eq:terminating-6phi5`) of the q-Pochhammer / q-binomial monograph.

## What is covered relative to the printed statement

* The `₆φ₅` summation itself is proved in full, over an **arbitrary field**, and with `a = 0`
  allowed.  The printed corollary asserts the identity in `ℚ(q,a,b,c)` and then specializes to
  `q,a,b,c ∈ ℂ^×`; the Lean statement is a specialized one.  Neither statement implies the
  other: Lean is more general in the ambient field and in dropping `a ≠ 0`, and less general in
  its nonvanishing hypotheses, which are strictly stronger than the printed ones (see below).
* `sixPhiFive_certificate` and `sixPhiFive_certificate_inv` — the single polynomial identity
  that carries the whole analytic content — hold over an **arbitrary commutative ring**
  (characteristic two and zero divisors included), and are stated there.
* `one_sub_mul_pow_mul_finiteQPochhammerIn`, `(1 - a q^k)(a;q)_k = (1 - a)(aq;q)_k`, is proved
  for **every** `k` over **every** commutative ring.  The corpus previously carried only
  `Fabius.one_sub_mul_pow_mul_finiteQPochhammerIn_two_mul` (`BaileyInversion`), the `k = 2n`
  case over a field, with the same proof; the general lemma subsumes it.

## What is NOT covered

1. `qg:thm-jackson-8phi7`, the terminating `₈φ₇` itself, is **not** proved here.  Nothing in
   this module depends on `FabiusFunction.JacksonRationalCertificate`.
2. The **printed derivation** of the corollary is not formalised.  The monograph obtains the
   `₆φ₅` from the `₈φ₇` by a coefficientwise rational limit `d → ∞`; the Lean proof below is a
   direct induction on `N` which never mentions `d`.  No defect in the printed argument is
   claimed: each side of `qg:eq:jackson-8phi7` is, after the stated cancellation of leading
   powers of `d`, a rational function of `x = 1/d` regular at `x = 0`, and a sum of `N+1` such
   terms is evaluated at `x = 0` termwise, exactly as the proof says.  The deviation is one of
   convenience — formalising that route needs the `₈φ₇` first, plus the limit apparatus,
   whereas the induction below needs neither.  A consequence is that the `₆φ₅` proved here is
   logically independent of the `₈φ₇` rather than a corollary of it.
3. The removable value `a = 1` of `qg:rem:jackson-a-one` is not covered; the hypothesis
   `a ≠ 1` stays.

## Hypotheses: slightly stronger than printed

The monograph asks `(1-a)(q, aq/b, aq/c, aq^{N+1};q)_N ≠ 0`.  The Lean statement asks

`q ≠ 0`, `b ≠ 0`, `c ≠ 0`, `a ≠ 1`, and
`(q;q)_{N+1} ≠ 0`, `(aq/b;q)_{N+1} ≠ 0`, `(aq/c;q)_{N+1} ≠ 0`, `(aq;q)_{2N+2} ≠ 0`.

`a ≠ 0` is deliberately absent: it is never used, and at `a = 0` every displayed symbol
degenerates to `1` and both sides equal `1`.

The index is `N+1` rather than `N` because the telescoping antiderivative reaches `k = n+2`,
and `(aq;q)_{2N+2}` replaces `(aq^{N+1};q)_N` because the induction visits every intermediate
`n ≤ N`, whose very-well-poised parameter is `a q^{n+1}`.  Concretely this excludes
`q^{m} = 1` for `1 ≤ m ≤ N+1` and requires `a q^m ≠ 1` for `1 ≤ m ≤ 2N+2` rather than only for
`N+1 ≤ m ≤ 2N`.

## The proof

Write `R_{n,k}` for the quotient of q-Pochhammer symbols of the `(n+1)`-st summand
(`sixPhiFiveR`) and set

`H_{n,k} = R_{n,k} (a q^{n+1}/(bc))^k (1 - a q^k/b)(1 - a q^k/c)(1 - a q^{n+k+1})(1 - q^k)
             / ((1-a)(1 - q^{-(n+1)}))`   (`sixPhiFiveH`).

Writing `T_{n,k}` for the `k`-th summand of the `n`-th sum (`sixPhiFiveTerm q a b c n k`), one
has `H_{n,0} = 0`, `H_{n,n+2} = 0`, `T_{n,n+1} = 0`, and

`(1 - a q^{n+1}/b)(1 - a q^{n+1}/c) T_{n+1,k} − (1 - a q^{n+1})(1 - a q^{n+1}/(bc)) T_{n,k}
   = H_{n,k+1} − H_{n,k}`   (`sixPhiFive_delta`).

Summing over `k < n+2` (`Finset.sum_range_sub`) gives the induction step.  After the
q-Pochhammer bookkeeping the whole difference collapses to the twenty-monomial identity
`sixPhiFive_certificate`, closed by `ring`.

## Main declarations

* `one_sub_mul_pow_mul_finiteQPochhammerIn` — the base-shift identity, all `k`, any `CommRing`.
* `sixPhiFive_certificate`, `sixPhiFive_certificate_inv` — the polynomial certificate.
* `sixPhiFiveTerm`, `sixPhiFiveProd` — the summand and the closed product.
* `sixPhiFiveTerm_self_succ_eq_zero` — the terminating factor kills the term at `k = N+1`.
* `sum_sixPhiFiveTerm` — the summation in terms of `sixPhiFiveTerm` / `sixPhiFiveProd`.
* `terminating_sixPhiFive` — the summation written out.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

variable {K : Type*} [Field K]

/-! ## Elementary q-Pochhammer facts -/

/-- If `(a;q)_n ≠ 0` then `(a;q)_m ≠ 0` for every `m ≤ n`.

This duplicates the public `Fabius.finiteQPochhammerIn_ne_zero_of_le` of
`FabiusFunction.QPfaffSaalschutz`.  It is repeated privately here because importing that module
would drag in the whole infinite-product analysis chain (`QPochhammerInfinite`, Tannery,
`Mathlib.Analysis.*`) for a three-line lemma. -/
private theorem finiteQPochhammerIn_ne_zero_of_le' (q a : K) {m n : ℕ} (h : m ≤ n)
    (hn : finiteQPochhammerIn a q n ≠ 0) : finiteQPochhammerIn a q m ≠ 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [finiteQPochhammerIn_add] at hn
  exact left_ne_zero_of_mul hn

/-- A nonvanishing finite q-Pochhammer symbol has nonvanishing factors. -/
private theorem finiteQPochhammerIn_factor_ne_zero (q a : K) (j : ℕ) {n : ℕ} (hj : j < n)
    (hn : finiteQPochhammerIn a q n ≠ 0) : (1 : K) - a * q ^ j ≠ 0 := by
  have h : (∏ i ∈ Finset.range n, (1 - a * q ^ i)) ≠ 0 := hn
  rw [Finset.prod_ne_zero_iff] at h
  exact h j (Finset.mem_range.mpr hj)

/-- **The base shift of a finite q-Pochhammer symbol.**  For every `k` over every commutative
ring, `(1 - a q^k) (a;q)_k = (1 - a) (aq;q)_k`.

`Fabius.one_sub_mul_pow_mul_finiteQPochhammerIn_two_mul` (`FabiusFunction.BaileyInversion`) is
the `k = 2n` case of this over a field, with the identical proof; this statement subsumes it and
needs neither inverses nor a nonvanishing hypothesis. -/
theorem one_sub_mul_pow_mul_finiteQPochhammerIn {R : Type*} [CommRing R] (a q : R) (k : ℕ) :
    (1 - a * q ^ k) * finiteQPochhammerIn a q k = (1 - a) * finiteQPochhammerIn (a * q) q k := by
  cases k with
  | zero => simp [finiteQPochhammerIn]
  | succ m =>
      rw [finiteQPochhammerIn_succ_shift a q m, finiteQPochhammerIn_succ (a * q) q m]
      ring

/-! ## The polynomial certificate -/

/-- **The `₆φ₅` certificate.**  With `X` standing for `q^{n+1}` and `y` for `q^k`,

`(1 - a y²) [ (b - aX)(c - aX) y (X - 1) − (X - y)(1 - aXy)(bc - aX) ]
  = aX (1 - ay)(1 - by)(1 - cy)(X - y) − X (b - ay)(c - ay)(1 - aXy)(1 - y)`.

Twenty monomials of total degree nine.  This single identity carries the whole analytic content
of the terminating `₆φ₅` summation, and it holds over an arbitrary commutative ring — no field,
no characteristic assumption, no nonvanishing hypothesis. -/
theorem sixPhiFive_certificate {R : Type*} [CommRing R] (a b c X y : R) :
    (1 - a * y ^ 2) *
        ((b - a * X) * (c - a * X) * y * (X - 1) -
          (X - y) * (1 - a * X * y) * (b * c - a * X))
      = a * X * (1 - a * y) * (1 - b * y) * (1 - c * y) * (X - y) -
        X * (b - a * y) * (c - a * y) * (1 - a * X * y) * (1 - y) := by
  ring

/-- **The `₆φ₅` certificate in inverse form.**  The same identity after dividing by `X` and
writing `w` for `X⁻¹`; it is the shape actually consumed by the telescoping step, where
`X = q^{n+1}` and `w = q^{-(n+1)}`.

Unlike `sixPhiFive_certificate` this is not a polynomial identity: it needs the relation
`w X = 1`, supplied as a hypothesis so that the statement still makes sense over an arbitrary
commutative ring (`w` need not be an inverse in the ring). -/
theorem sixPhiFive_certificate_inv {R : Type*} [CommRing R] (a b c X w y : R) (hwX : w * X = 1) :
    (1 - a * y ^ 2) *
        ((b - a * X) * (c - a * X) * y * (1 - w) -
          (b * c - a * X) * (1 - w * y) * (1 - a * X * y))
      = a * X * (1 - a * y) * (1 - b * y) * (1 - c * y) * (1 - w * y) -
        (b - a * y) * (c - a * y) * (1 - a * X * y) * (1 - y) := by
  linear_combination
    (-(a * y * (y - 1) * (a ^ 2 * X * y ^ 2 - a * X - a * y - b * c * y + b + c))) * hwX

/-! ## The summand, the product, and the telescoping antiderivative -/

/-- The `k`-th summand of the terminating very-well-poised `₆φ₅` at upper index `n`:

`(1 - a q^{2k})/(1-a) · (a,b,c,q^{-n};q)_k / ((q, aq/b, aq/c, a q^{n+1};q)_k)
   · (a q^{n+1}/(bc))^k`. -/
def sixPhiFiveTerm (q a b c : K) (n k : ℕ) : K :=
  (1 - a * q ^ (2 * k)) / (1 - a) *
      (finiteQPochhammerIn a q k * finiteQPochhammerIn b q k * finiteQPochhammerIn c q k *
        finiteQPochhammerIn (q ^ n)⁻¹ q k) /
      (finiteQPochhammerIn q q k * finiteQPochhammerIn (a * q / b) q k *
        finiteQPochhammerIn (a * q / c) q k * finiteQPochhammerIn (a * q ^ (n + 1)) q k) *
    (a * q ^ (n + 1) / (b * c)) ^ k

/-- The closed product on the right of the terminating `₆φ₅`:
`(aq, aq/(bc);q)_n / ((aq/b, aq/c;q)_n)`. -/
def sixPhiFiveProd (q a b c : K) (n : ℕ) : K :=
  finiteQPochhammerIn (a * q) q n * finiteQPochhammerIn (a * q / (b * c)) q n /
    (finiteQPochhammerIn (a * q / b) q n * finiteQPochhammerIn (a * q / c) q n)

/-- **The sum terminates.**  The factor `(q^{-n};q)_k` vanishes for `k = n+1`, so the summand
does. -/
theorem sixPhiFiveTerm_self_succ_eq_zero (q a b c : K) (n : ℕ) (hq0 : q ≠ 0) :
    sixPhiFiveTerm q a b c n (n + 1) = 0 := by
  have h : finiteQPochhammerIn (q ^ n)⁻¹ q (n + 1) = 0 :=
    finiteQPochhammerIn_inv_pow_eq_zero_of_lt q hq0 (by omega)
  unfold sixPhiFiveTerm
  rw [h, mul_zero, mul_zero, zero_div, zero_mul]

/-- The q-Pochhammer quotient shared by the `(n+1)`-st summand and by the telescoping
antiderivative:
`(a,b,c,q^{-(n+1)};q)_k / ((q, aq/b, aq/c, a q^{n+2};q)_k)`. -/
private def sixPhiFiveR (q a b c : K) (n k : ℕ) : K :=
  finiteQPochhammerIn a q k * finiteQPochhammerIn b q k * finiteQPochhammerIn c q k *
      finiteQPochhammerIn (q ^ (n + 1))⁻¹ q k /
    (finiteQPochhammerIn q q k * finiteQPochhammerIn (a * q / b) q k *
      finiteQPochhammerIn (a * q / c) q k * finiteQPochhammerIn (a * q ^ (n + 1 + 1)) q k)

/-- The telescoping antiderivative `H_{n,k}` of the `₆φ₅` induction step. -/
private def sixPhiFiveH (q a b c : K) (n k : ℕ) : K :=
  sixPhiFiveR q a b c n k * (a * q ^ (n + 1) / (b * c)) ^ k *
      ((1 - a * q ^ k / b) * (1 - a * q ^ k / c) * (1 - a * q ^ (n + 1) * q ^ k) *
        (1 - q ^ k)) /
    ((1 - a) * (1 - (q ^ (n + 1))⁻¹))

/-! ## Purely algebraic auxiliaries

Each of these is stated with plain variables so that every occurrence of an inverse is an
inverse of a single atom; that keeps `ring` and `field_simp` on ground they can handle. -/

/-- Rewriting a quotient of products after one numerator and one denominator factor have been
replaced by quotients.  Purely multiplicative, hence valid with no nonvanishing hypotheses
(both sides are `0` when any of `v`, `t`, `s`, `Q4` vanishes).

The `div_div_eq_mul_div` step is not cosmetic: `ring` inverts a monomial by inverting each of
its base atoms, so an inverse of an expression that itself contains `t⁻¹` would introduce the
atom `(t⁻¹)⁻¹`, which `ring` does not identify with `t`.  Clearing the inner division first
keeps every inverse an inverse of a plain atom. -/
private theorem sixPhiFive_nest_aux (E Za P1 P2 P3 P4 Q1 Q2 Q3 Q4 u v s t : K) :
    E * (P1 * P2 * P3 * (u * P4 / v)) / (Q1 * Q2 * Q3 * (s * Q4 / t)) * Za
      = E * (P1 * P2 * P3 * P4 / (Q1 * Q2 * Q3 * Q4)) * Za * (u * t) / (v * s) := by
  rw [show Q1 * Q2 * Q3 * (s * Q4 / t) = Q1 * Q2 * Q3 * (s * Q4) / t by ring,
    div_div_eq_mul_div]
  ring

/-- Cancelling the denominator introduced by the `R`-recursion against the vanishing factor of
the antiderivative. -/
private theorem sixPhiFive_cancel_aux (R U V T D : K) (hV : V ≠ 0) :
    R * (U / V) * T * V / D = R * T * U / D := by
  rw [show R * (U / V) * T * V = R * T * (U / V * V) by ring, div_mul_cancel₀ U hV]

/-- Splitting the four factors adjoined to a fourfold quotient by one step of the q-Pochhammer
recursion.  Every inverse here is an inverse of a plain atom, which is what lets `ring` close
it. -/
private theorem sixPhiFiveR_quot_aux (P1 P2 P3 P4 Q1 Q2 Q3 Q4 u1 u2 u3 u4 v1 v2 v3 v4 : K) :
    P1 * u1 * (P2 * u2) * (P3 * u3) * (P4 * u4) /
        (Q1 * v1 * (Q2 * v2) * (Q3 * v3) * (Q4 * v4))
      = P1 * P2 * P3 * P4 / (Q1 * Q2 * Q3 * Q4) *
        (u1 * u2 * u3 * u4 / (v2 * v3 * v4 * v1)) := by
  ring

/-- Cancelling the two factors adjoined to the closed product. -/
private theorem sixPhiFiveProd_cancel_aux (A B C D s t u v : K) (hC : C ≠ 0) (hD : D ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    A * s * (B * t) / (C * u * (D * v)) * (u * v) = A * B / (C * D) * (s * t) := by
  field_simp <;> ring

/-! ## The recursions -/

/-- The one-step recursion of the q-Pochhammer quotient `R_{n,k}`.  No hypotheses: both sides
are the same quotient of the same two products. -/
private theorem sixPhiFiveR_succ (q a b c : K) (n k : ℕ) :
    sixPhiFiveR q a b c n (k + 1)
      = sixPhiFiveR q a b c n k *
        (((1 - a * q ^ k) * (1 - b * q ^ k) * (1 - c * q ^ k) *
            (1 - (q ^ (n + 1))⁻¹ * q ^ k)) /
          ((1 - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
            (1 - a * q ^ (n + 1 + 1) * q ^ k) * (1 - q * q ^ k))) := by
  unfold sixPhiFiveR
  simp only [finiteQPochhammerIn_succ]
  exact sixPhiFiveR_quot_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The antiderivative vanishes at `k = 0`: its factor `1 - q^0` does. -/
private theorem sixPhiFiveH_zero (q a b c : K) (n : ℕ) : sixPhiFiveH q a b c n 0 = 0 := by
  simp [sixPhiFiveH]

/-- The antiderivative vanishes at `k = n+2`: the terminating factor `(q^{-(n+1)};q)_{n+2}`
does. -/
private theorem sixPhiFiveH_top (q a b c : K) (n : ℕ) (hq0 : q ≠ 0) :
    sixPhiFiveH q a b c n (n + 1 + 1) = 0 := by
  have h : finiteQPochhammerIn (q ^ (n + 1))⁻¹ q (n + 1 + 1) = 0 :=
    finiteQPochhammerIn_inv_pow_eq_zero_of_lt q hq0 (by omega)
  have hR : sixPhiFiveR q a b c n (n + 1 + 1) = 0 := by
    unfold sixPhiFiveR
    rw [h, mul_zero, zero_div]
  unfold sixPhiFiveH
  rw [hR, zero_mul, zero_mul, zero_div]

/-- The one-step recursion of the antiderivative: the four factors adjoined to the denominator
of `R_{n,k+1}` are exactly the four factors of `H_{n,k+1}`, and they cancel. -/
private theorem sixPhiFiveH_succ (q a b c : K) (n k : ℕ)
    (hV : ((1 : K) - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
      (1 - a * q ^ (n + 1 + 1) * q ^ k) * (1 - q * q ^ k) ≠ 0) :
    sixPhiFiveH q a b c n (k + 1)
      = sixPhiFiveR q a b c n k *
          ((a * q ^ (n + 1) / (b * c)) ^ k * (a * q ^ (n + 1) / (b * c))) *
          ((1 - a * q ^ k) * (1 - b * q ^ k) * (1 - c * q ^ k) *
            (1 - (q ^ (n + 1))⁻¹ * q ^ k)) /
        ((1 - a) * (1 - (q ^ (n + 1))⁻¹)) := by
  have hvfac : ((1 : K) - a * q ^ (k + 1) / b) * (1 - a * q ^ (k + 1) / c) *
      (1 - a * q ^ (n + 1) * q ^ (k + 1)) * (1 - q ^ (k + 1))
      = ((1 : K) - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
        (1 - a * q ^ (n + 1 + 1) * q ^ k) * (1 - q * q ^ k) := by
    ring
  have hZ : (a * q ^ (n + 1) / (b * c)) ^ (k + 1)
      = (a * q ^ (n + 1) / (b * c)) ^ k * (a * q ^ (n + 1) / (b * c)) :=
    pow_succ _ _
  unfold sixPhiFiveH
  rw [sixPhiFiveR_succ q a b c n k, hvfac, hZ]
  exact sixPhiFive_cancel_aux _ _ _ _ _ hV

/-- The `(n+1)`-st summand in terms of `R_{n,k}`: the six q-Pochhammer symbols already agree,
only the geometric factor changes, by `q^k`. -/
private theorem sixPhiFiveTerm_succ_eq (q a b c : K) (n k : ℕ) :
    sixPhiFiveTerm q a b c (n + 1) k
      = (1 - a * q ^ (2 * k)) / (1 - a) * sixPhiFiveR q a b c n k *
        ((a * q ^ (n + 1) / (b * c)) ^ k * q ^ k) := by
  have hz : a * q ^ (n + 1 + 1) / (b * c) = a * q ^ (n + 1) / (b * c) * q := by ring
  unfold sixPhiFiveTerm sixPhiFiveR
  rw [hz, mul_pow]
  ring

/-- The `n`-th summand in terms of `R_{n,k}`.  Two applications of
`one_sub_mul_pow_mul_finiteQPochhammerIn` move `(q^{-n};q)_k` to `(q^{-(n+1)};q)_k` and
`(a q^{n+1};q)_k` to `(a q^{n+2};q)_k`. -/
private theorem sixPhiFiveTerm_eq (q a b c : K) (n k : ℕ) (hq0 : q ≠ 0)
    (hw1 : (1 : K) - (q ^ (n + 1))⁻¹ ≠ 0)
    (haxk : (1 : K) - a * q ^ (n + 1) * q ^ k ≠ 0) :
    sixPhiFiveTerm q a b c n k
      = (1 - a * q ^ (2 * k)) / (1 - a) * sixPhiFiveR q a b c n k *
          (a * q ^ (n + 1) / (b * c)) ^ k *
          ((1 - (q ^ (n + 1))⁻¹ * q ^ k) * (1 - a * q ^ (n + 1) * q ^ k)) /
        ((1 - (q ^ (n + 1))⁻¹) * (1 - a * q ^ (n + 1))) := by
  have hinv : (q ^ (n + 1))⁻¹ * q = (q ^ n)⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
  have h1 : (1 - (q ^ (n + 1))⁻¹ * q ^ k) * finiteQPochhammerIn (q ^ (n + 1))⁻¹ q k
      = (1 - (q ^ (n + 1))⁻¹) * finiteQPochhammerIn (q ^ n)⁻¹ q k := by
    rw [← hinv]
    exact one_sub_mul_pow_mul_finiteQPochhammerIn _ q k
  have h2 : (1 - a * q ^ (n + 1) * q ^ k) * finiteQPochhammerIn (a * q ^ (n + 1)) q k
      = (1 - a * q ^ (n + 1)) * finiteQPochhammerIn (a * q ^ (n + 1 + 1)) q k := by
    have h := one_sub_mul_pow_mul_finiteQPochhammerIn (a * q ^ (n + 1)) q k
    rwa [show a * q ^ (n + 1) * q = a * q ^ (n + 1 + 1) by ring] at h
  have h1' : finiteQPochhammerIn (q ^ n)⁻¹ q k
      = (1 - (q ^ (n + 1))⁻¹ * q ^ k) * finiteQPochhammerIn (q ^ (n + 1))⁻¹ q k /
        (1 - (q ^ (n + 1))⁻¹) := by
    rw [eq_div_iff hw1, h1]; ring
  have h2' : finiteQPochhammerIn (a * q ^ (n + 1)) q k
      = (1 - a * q ^ (n + 1)) * finiteQPochhammerIn (a * q ^ (n + 1 + 1)) q k /
        (1 - a * q ^ (n + 1) * q ^ k) := by
    rw [eq_div_iff haxk, ← h2]; ring
  unfold sixPhiFiveTerm sixPhiFiveR
  rw [h1', h2']
  exact sixPhiFive_nest_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The telescoping step -/

set_option maxHeartbeats 1000000 in
/-- The scalar identity behind the telescoping step, with the q-Pochhammer quotient `R` and the
geometric factor `Z` as opaque parameters.  Both sides are the common factor
`R Z / ((1-a)(1-w) b c)` times the two sides of `sixPhiFive_certificate_inv`. -/
private theorem sixPhiFive_delta_scalar (a b c X w y R Z : K) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (h1a : (1 : K) - a ≠ 0) (hw1 : (1 : K) - w ≠ 0) (hax : (1 : K) - a * X ≠ 0)
    (hwX : w * X = 1) :
    (1 - a * X / b) * (1 - a * X / c) * ((1 - a * y ^ 2) / (1 - a) * R * (Z * y)) -
        (1 - a * X) * (1 - a * X / (b * c)) *
          ((1 - a * y ^ 2) / (1 - a) * R * Z *
            ((1 - w * y) * (1 - a * X * y)) / ((1 - w) * (1 - a * X)))
      = R * (Z * (a * X / (b * c))) *
          ((1 - a * y) * (1 - b * y) * (1 - c * y) * (1 - w * y)) / ((1 - a) * (1 - w)) -
        R * Z * ((1 - a * y / b) * (1 - a * y / c) * (1 - a * X * y) * (1 - y)) /
          ((1 - a) * (1 - w)) := by
  have hL : (1 - a * X / b) * (1 - a * X / c) * ((1 - a * y ^ 2) / (1 - a) * R * (Z * y)) -
        (1 - a * X) * (1 - a * X / (b * c)) *
          ((1 - a * y ^ 2) / (1 - a) * R * Z *
            ((1 - w * y) * (1 - a * X * y)) / ((1 - w) * (1 - a * X)))
      = R * Z / ((1 - a) * (1 - w) * (b * c)) *
        ((1 - a * y ^ 2) *
          ((b - a * X) * (c - a * X) * y * (1 - w) -
            (b * c - a * X) * (1 - w * y) * (1 - a * X * y))) := by
    field_simp <;> ring
  have hR : R * (Z * (a * X / (b * c))) *
        ((1 - a * y) * (1 - b * y) * (1 - c * y) * (1 - w * y)) / ((1 - a) * (1 - w)) -
        R * Z * ((1 - a * y / b) * (1 - a * y / c) * (1 - a * X * y) * (1 - y)) /
          ((1 - a) * (1 - w))
      = R * Z / ((1 - a) * (1 - w) * (b * c)) *
        (a * X * (1 - a * y) * (1 - b * y) * (1 - c * y) * (1 - w * y) -
          (b - a * y) * (c - a * y) * (1 - a * X * y) * (1 - y)) := by
    field_simp <;> ring
  rw [hL, hR, sixPhiFive_certificate_inv a b c X w y hwX]

/-- **The telescoping step.**  Pointwise in `k`,

`(1 - a q^{n+1}/b)(1 - a q^{n+1}/c) T_{n+1,k} − (1 - a q^{n+1})(1 - a q^{n+1}/(bc)) T_{n,k}
   = H_{n,k+1} − H_{n,k}`. -/
private theorem sixPhiFive_delta (q a b c : K) (n k : ℕ) (hq0 : q ≠ 0) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) (h1a : (1 : K) - a ≠ 0) (hw1 : (1 : K) - (q ^ (n + 1))⁻¹ ≠ 0)
    (hax : (1 : K) - a * q ^ (n + 1) ≠ 0)
    (haxk : (1 : K) - a * q ^ (n + 1) * q ^ k ≠ 0)
    (hV : ((1 : K) - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
      (1 - a * q ^ (n + 1 + 1) * q ^ k) * (1 - q * q ^ k) ≠ 0) :
    (1 - a * q ^ (n + 1) / b) * (1 - a * q ^ (n + 1) / c) * sixPhiFiveTerm q a b c (n + 1) k -
        (1 - a * q ^ (n + 1)) * (1 - a * q ^ (n + 1) / (b * c)) * sixPhiFiveTerm q a b c n k
      = sixPhiFiveH q a b c n (k + 1) - sixPhiFiveH q a b c n k := by
  have hqk2 : q ^ (2 * k) = (q ^ k) ^ 2 := by rw [two_mul, pow_add, pow_two]
  have hwX : (q ^ (n + 1))⁻¹ * q ^ (n + 1) = 1 := inv_mul_cancel₀ (pow_ne_zero _ hq0)
  rw [sixPhiFiveTerm_succ_eq q a b c n k, sixPhiFiveTerm_eq q a b c n k hq0 hw1 haxk,
    sixPhiFiveH_succ q a b c n k hV]
  unfold sixPhiFiveH
  rw [hqk2]
  exact sixPhiFive_delta_scalar a b c (q ^ (n + 1)) ((q ^ (n + 1))⁻¹) (q ^ k)
    (sixPhiFiveR q a b c n k) ((a * q ^ (n + 1) / (b * c)) ^ k) hb0 hc0 h1a hw1 hax hwX

/-- The one-step recursion of the closed product. -/
private theorem sixPhiFiveProd_succ (q a b c : K) (n : ℕ)
    (hu : (1 : K) - a * q ^ (n + 1) / b ≠ 0) (hv : (1 : K) - a * q ^ (n + 1) / c ≠ 0)
    (hPb : finiteQPochhammerIn (a * q / b) q n ≠ 0)
    (hPc : finiteQPochhammerIn (a * q / c) q n ≠ 0) :
    sixPhiFiveProd q a b c (n + 1) *
        ((1 - a * q ^ (n + 1) / b) * (1 - a * q ^ (n + 1) / c))
      = sixPhiFiveProd q a b c n *
        ((1 - a * q ^ (n + 1)) * (1 - a * q ^ (n + 1) / (b * c))) := by
  unfold sixPhiFiveProd
  simp only [finiteQPochhammerIn_succ]
  rw [show a * q * q ^ n = a * q ^ (n + 1) by ring,
    show a * q / (b * c) * q ^ n = a * q ^ (n + 1) / (b * c) by ring,
    show a * q / b * q ^ n = a * q ^ (n + 1) / b by ring,
    show a * q / c * q ^ n = a * q ^ (n + 1) / c by ring]
  exact sixPhiFiveProd_cancel_aux _ _ _ _ _ _ _ _ hPb hPc hu hv

/-- **The induction step for the sums.**  Summing `sixPhiFive_delta` over `k < n+2` telescopes
to zero; the top term of the `n`-th sum vanishes by `sixPhiFiveTerm_self_succ_eq_zero`. -/
private theorem sixPhiFive_step (q a b c : K) (n : ℕ) (hq0 : q ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (h1a : (1 : K) - a ≠ 0) (hw1 : (1 : K) - (q ^ (n + 1))⁻¹ ≠ 0)
    (hax : (1 : K) - a * q ^ (n + 1) ≠ 0)
    (haxk : ∀ k, k < n + 1 + 1 → (1 : K) - a * q ^ (n + 1) * q ^ k ≠ 0)
    (hbk : ∀ k, k < n + 1 + 1 → (1 : K) - a * q / b * q ^ k ≠ 0)
    (hck : ∀ k, k < n + 1 + 1 → (1 : K) - a * q / c * q ^ k ≠ 0)
    (hdk : ∀ k, k < n + 1 + 1 → (1 : K) - a * q ^ (n + 1 + 1) * q ^ k ≠ 0)
    (hqk : ∀ k, k < n + 1 + 1 → (1 : K) - q * q ^ k ≠ 0) :
    (1 - a * q ^ (n + 1) / b) * (1 - a * q ^ (n + 1) / c) *
        ∑ k ∈ Finset.range (n + 1 + 1), sixPhiFiveTerm q a b c (n + 1) k
      = (1 - a * q ^ (n + 1)) * (1 - a * q ^ (n + 1) / (b * c)) *
        ∑ k ∈ Finset.range (n + 1), sixPhiFiveTerm q a b c n k := by
  have hterm0 : ∑ k ∈ Finset.range (n + 1 + 1), sixPhiFiveTerm q a b c n k
      = ∑ k ∈ Finset.range (n + 1), sixPhiFiveTerm q a b c n k := by
    rw [Finset.sum_range_succ, sixPhiFiveTerm_self_succ_eq_zero q a b c n hq0, add_zero]
  have htel : ∑ k ∈ Finset.range (n + 1 + 1),
        (sixPhiFiveH q a b c n (k + 1) - sixPhiFiveH q a b c n k)
      = sixPhiFiveH q a b c n (n + 1 + 1) - sixPhiFiveH q a b c n 0 :=
    Finset.sum_range_sub (fun k => sixPhiFiveH q a b c n k) (n + 1 + 1)
  have htel0 : ∑ k ∈ Finset.range (n + 1 + 1),
      (sixPhiFiveH q a b c n (k + 1) - sixPhiFiveH q a b c n k) = 0 := by
    rw [htel, sixPhiFiveH_top q a b c n hq0, sixPhiFiveH_zero q a b c n, sub_zero]
  have hdelta : (1 - a * q ^ (n + 1) / b) * (1 - a * q ^ (n + 1) / c) *
        (∑ k ∈ Finset.range (n + 1 + 1), sixPhiFiveTerm q a b c (n + 1) k) -
        (1 - a * q ^ (n + 1)) * (1 - a * q ^ (n + 1) / (b * c)) *
          (∑ k ∈ Finset.range (n + 1 + 1), sixPhiFiveTerm q a b c n k) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← htel0]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n + 1 + 1 := Finset.mem_range.mp hk
    exact sixPhiFive_delta q a b c n k hq0 hb0 hc0 h1a hw1 hax (haxk k hk')
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hbk k hk') (hck k hk')) (hdk k hk'))
        (hqk k hk'))
  rw [← hterm0]
  exact sub_eq_zero.mp hdelta

/-! ## The summation -/

/-- **The terminating very-well-poised `₆φ₅` summation**, stated with `sixPhiFiveTerm` and
`sixPhiFiveProd`.  See `terminating_sixPhiFive` for the written-out form and the module
docstring for the exact relation to `qg:cor-jackson-6phi5`. -/
theorem sum_sixPhiFiveTerm (q a b c : K) (hq0 : q ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (ha1 : a ≠ 1) : ∀ N : ℕ,
    finiteQPochhammerIn q q (N + 1) ≠ 0 →
    finiteQPochhammerIn (a * q / b) q (N + 1) ≠ 0 →
    finiteQPochhammerIn (a * q / c) q (N + 1) ≠ 0 →
    finiteQPochhammerIn (a * q) q (2 * N + 2) ≠ 0 →
    ∑ k ∈ Finset.range (N + 1), sixPhiFiveTerm q a b c N k = sixPhiFiveProd q a b c N := by
  have h1a : (1 : K) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  intro N
  induction N with
  | zero =>
      intro _ _ _ _
      simp [sixPhiFiveTerm, sixPhiFiveProd, div_self h1a]
  | succ n ih =>
      intro hQ hB hC hA
      -- restrict the hypotheses to the previous index
      have hQ' : finiteQPochhammerIn q q (n + 1) ≠ 0 :=
        finiteQPochhammerIn_ne_zero_of_le' q q (by omega) hQ
      have hB' : finiteQPochhammerIn (a * q / b) q (n + 1) ≠ 0 :=
        finiteQPochhammerIn_ne_zero_of_le' q (a * q / b) (by omega) hB
      have hC' : finiteQPochhammerIn (a * q / c) q (n + 1) ≠ 0 :=
        finiteQPochhammerIn_ne_zero_of_le' q (a * q / c) (by omega) hC
      have hA' : finiteQPochhammerIn (a * q) q (2 * n + 2) ≠ 0 :=
        finiteQPochhammerIn_ne_zero_of_le' q (a * q) (by omega) hA
      have ihres := ih hQ' hB' hC' hA'
      -- the individual nonvanishing factors
      have hqfac : ∀ j, j < n + 1 + 1 → (1 : K) - q * q ^ j ≠ 0 := fun j hj =>
        finiteQPochhammerIn_factor_ne_zero q q j hj hQ
      have hbfac : ∀ j, j < n + 1 + 1 → (1 : K) - a * q / b * q ^ j ≠ 0 := fun j hj =>
        finiteQPochhammerIn_factor_ne_zero q (a * q / b) j hj hB
      have hcfac : ∀ j, j < n + 1 + 1 → (1 : K) - a * q / c * q ^ j ≠ 0 := fun j hj =>
        finiteQPochhammerIn_factor_ne_zero q (a * q / c) j hj hC
      have hafac : ∀ j, j < 2 * (n + 1) + 2 → (1 : K) - a * q * q ^ j ≠ 0 := fun j hj =>
        finiteQPochhammerIn_factor_ne_zero q (a * q) j hj hA
      have hax : (1 : K) - a * q ^ (n + 1) ≠ 0 := by
        have h := hafac n (by omega)
        rwa [show a * q * q ^ n = a * q ^ (n + 1) by ring] at h
      have haxk : ∀ k, k < n + 1 + 1 → (1 : K) - a * q ^ (n + 1) * q ^ k ≠ 0 := by
        intro k hk
        have h := hafac (n + k) (by omega)
        rwa [show a * q * q ^ (n + k) = a * q ^ (n + 1) * q ^ k by ring] at h
      have hdk : ∀ k, k < n + 1 + 1 → (1 : K) - a * q ^ (n + 1 + 1) * q ^ k ≠ 0 := by
        intro k hk
        have h := hafac (n + 1 + k) (by omega)
        rwa [show a * q * q ^ (n + 1 + k) = a * q ^ (n + 1 + 1) * q ^ k by ring] at h
      have hu : (1 : K) - a * q ^ (n + 1) / b ≠ 0 := by
        have h := hbfac n (by omega)
        rwa [show a * q / b * q ^ n = a * q ^ (n + 1) / b by ring] at h
      have hv : (1 : K) - a * q ^ (n + 1) / c ≠ 0 := by
        have h := hcfac n (by omega)
        rwa [show a * q / c * q ^ n = a * q ^ (n + 1) / c by ring] at h
      have hqpow : q ^ (n + 1) ≠ 1 := by
        intro h
        refine hqfac n (by omega) ?_
        rw [show q * q ^ n = q ^ (n + 1) by ring, h, sub_self]
      have hw1 : (1 : K) - (q ^ (n + 1))⁻¹ ≠ 0 := by
        apply sub_ne_zero.mpr
        intro h
        apply hqpow
        rw [← inv_inv (q ^ (n + 1)), ← h, inv_one]
      have hPb : finiteQPochhammerIn (a * q / b) q n ≠ 0 :=
        finiteQPochhammerIn_ne_zero_of_le' q (a * q / b) (by omega) hB
      have hPc : finiteQPochhammerIn (a * q / c) q n ≠ 0 :=
        finiteQPochhammerIn_ne_zero_of_le' q (a * q / c) (by omega) hC
      have hprod := sixPhiFiveProd_succ q a b c n hu hv hPb hPc
      have hstep := sixPhiFive_step q a b c n hq0 hb0 hc0 h1a hw1 hax haxk hbfac hcfac hdk
        hqfac
      have hgoal : (1 - a * q ^ (n + 1) / b) * (1 - a * q ^ (n + 1) / c) *
            ∑ k ∈ Finset.range (n + 1 + 1), sixPhiFiveTerm q a b c (n + 1) k
          = (1 - a * q ^ (n + 1) / b) * (1 - a * q ^ (n + 1) / c) *
            sixPhiFiveProd q a b c (n + 1) := by
        rw [hstep, ihres]
        linear_combination (-1 : K) * hprod
      exact mul_left_cancel₀ (mul_ne_zero hu hv) hgoal

/-- **The terminating very-well-poised `₆φ₅` summation**, written out.  For `q, b, c ≠ 0`,
`a ≠ 1` and `(q;q)_{N+1}`, `(aq/b;q)_{N+1}`, `(aq/c;q)_{N+1}`, `(aq;q)_{2N+2}` all nonzero,

`∑_{k=0}^{N} (1 - a q^{2k})/(1-a) · (a,b,c,q^{-N};q)_k / ((q, aq/b, aq/c, a q^{N+1};q)_k)
   · (a q^{N+1}/(bc))^k = (aq, aq/(bc);q)_N / ((aq/b, aq/c;q)_N)`,

with `q^{-N}` written `(q ^ N)⁻¹`.  The field is arbitrary; the printed corollary
`qg:cor-jackson-6phi5` states the complex case.  The hypotheses are slightly stronger than the
printed `(1-a)(q, aq/b, aq/c, aq^{N+1};q)_N ≠ 0`; see the module docstring. -/
theorem terminating_sixPhiFive (q a b c : K) (hq0 : q ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (ha1 : a ≠ 1) (N : ℕ) (hQ : finiteQPochhammerIn q q (N + 1) ≠ 0)
    (hB : finiteQPochhammerIn (a * q / b) q (N + 1) ≠ 0)
    (hC : finiteQPochhammerIn (a * q / c) q (N + 1) ≠ 0)
    (hA : finiteQPochhammerIn (a * q) q (2 * N + 2) ≠ 0) :
    ∑ k ∈ Finset.range (N + 1),
        (1 - a * q ^ (2 * k)) / (1 - a) *
            (finiteQPochhammerIn a q k * finiteQPochhammerIn b q k *
              finiteQPochhammerIn c q k * finiteQPochhammerIn (q ^ N)⁻¹ q k) /
            (finiteQPochhammerIn q q k * finiteQPochhammerIn (a * q / b) q k *
              finiteQPochhammerIn (a * q / c) q k *
              finiteQPochhammerIn (a * q ^ (N + 1)) q k) *
          (a * q ^ (N + 1) / (b * c)) ^ k
      = finiteQPochhammerIn (a * q) q N * finiteQPochhammerIn (a * q / (b * c)) q N /
        (finiteQPochhammerIn (a * q / b) q N * finiteQPochhammerIn (a * q / c) q N) :=
  sum_sixPhiFiveTerm q a b c hq0 hb0 hc0 ha1 N hQ hB hC hA

end Fabius
