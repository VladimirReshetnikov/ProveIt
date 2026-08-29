import FabiusFunction.LobeSignLaw
import FabiusFunction.IntegerZeroAnalyticOrder

/-!
# The canonical product at an integer point

`FabiusFunction.LobeSignLaw` proves the exponent-sequence volume's
sign law on the *open* lobes: for `N < x < N + 1`,
`sgn Φ_a(x) = ε_a(N)`.  Its own docstring records the resulting gap,
and so does the volume, in the scope caveat attached to
`p1:thm:lobe-sign`:

> "the display above is qualified here *away from the integer points
> altogether*, whereas \eqref{p1:eq:sign-master} is stated 'away from
> the integer zeros'.  An integer $x$ at which no factor of $\Phi_a$
> vanishes --- possible when $a$ has zero layers --- falls inside the
> volume's claim and outside the formalized one."

This module closes that gap, and adds the factorization of the
canonical product at a single index.

## Part one: the integer point

At `x = n` the canonical factor of index `n` is `0 ^ (m_a n)`, which
is `1` exactly when `m_a n = 0`.  Under that hypothesis the split of
`LobeSignLaw` still applies, with one change: the index `m + 1 = n` of
the prefix now contributes the factor `1` instead of a negative
number, and it may be kept in or dropped from the exponent count
freely because its exponent is `0`.  Everything else is verbatim:
indices `m + 1 < n` have a negative base, indices `m + 1 > n` a
positive one, and the tail is positive because its logarithm series
converges.  The conclusion is the *same* formula as on the lobes,

`0 < ε_a(n) · Ψ_a(n)`,

so `p1:eq:sign-master` now holds at every real `x > 0` at which no
factor of `Φ_a` vanishes: for non-integer `x` by `LobeSignLaw` at
`N = ⌊x⌋`, and for an integer `n ≥ 1` by this module, whose
hypothesis `m_a n = 0` is exactly "no factor vanishes" there.

Two points of the volume's own phrasing are *not* covered.  At
`x = 0` no factor vanishes and `Φ_a(0) = 1`, but the hypothesis below
reads `m_a 0 = a 0`, which need not be zero — that case is closed
separately by `canonicalRealProduct_zero_eq_one`.  Negative arguments
are not treated at all: `Φ_a` is even, so the law there reads
`ε_a(⌊|x|⌋)` rather than `ε_a(⌊x⌋)`, and neither file states it.

The hypothesis is sharp in the other direction as well: for
`n ≥ 1`, if `m_a n ≠ 0` then `Φ_a(n) = 0`.  At `n = 0` it is not:
`m_a 0 = a 0` may be nonzero while `Φ_a(0) = 1`.  That converse is
not reproved here; it is read off the corpus's
`Fabius.generalizedRvachevProduct_eq_zero_iff`.

## Part two: the factored form at one index

For `n = m + 1 ≥ 1` the canonical product splits at the single index
`n`,

`Φ_a(z) = (1 - z²/n²) ^ (m_a n) · R_n(z)`,

where `R_n` is the product of all the *other* canonical factors, and
`R_n(±n) ≠ 0`.

**This is not an order-of-vanishing statement.**  The volume asserts,
alongside `p1:eq:canonical-a` in `p1:thm:zero-zeta`, "In particular,
`ord_{z=±n} Φ_a = m_a(n)`".  That is a statement about
`analyticOrderAt`, and it needs analyticity of `Φ_a`, hence
convergence uniform on compact sets.  The corpus has that whole
story at the *constant* weight — `rvachevFourierProduct_differentiable`
and `analyticOrderAt_rvachevFourierProduct_int` in
`FabiusFunction.IntegerZeroAnalyticOrder` — and the resulting
instance of the display is recorded below as
`analyticOrderAt_generalizedRvachevProduct_one`.  For a general
admissible `a` nothing supplies analyticity.  What is proved
here is the algebraic input to such a statement: the factorization
itself, together with the nonvanishing of the complementary factor at
the two candidate zeros.  Turning it into an order statement would
require, in addition, that `R_n` be analytic near `±n` — not proved
anywhere in the corpus.

The split of a `tprod` at a single index uses Mathlib's
`Multipliable.tprod_eq_mul_tprod_ite'`, the `CommMonoid` form, whose
convergence hypothesis is phrased with `Function.update`; the
`CommGroup` form `Multipliable.tprod_eq_mul_tprod_ite` is unavailable
because `ℂ` is not a topological group under multiplication.  The
nonvanishing reuses the shape of
`Fabius.generalizedRvachevProduct_ne_zero`: absolute summability of
the factor deviations is the hypothesis of Mathlib's
`tprod_one_add_ne_zero_of_summable`.

## Numerical check

The statements were checked numerically before being proved, at
weights with zero layers.  For `a = δ₁` (`a 1 = 1`, else `0`) one has
`m_a(n) = 0` exactly for odd `n` and `Φ_a(z) = sinc (z/2)`:
`Φ(1) = 0.63662`, `Φ(3) = -0.21221`, `Φ(5) = 0.12732`,
`Φ(7) = -0.09095`, against `ε_a(n) = (-1)^(b₁(n))`, which is
`+,-,+,-`.  For `a = δ₂` the zero set is `4ℕ` and
`Φ(1..3) > 0 > Φ(5..7)`, against `ε_a(n) = (-1)^(b₂(n))`.  For
`a = (0,2,1,0,…)` the values at `n = 1,3,5,7` are
`0.36488, 0.013514, -0.0029191, -0.0010638`, again matching.  The
complementary factors `R_n(±n)` were computed as truncated products
and are nonzero in every case, including the cases `m_a(n) ≠ 0` where
`Φ_a(n) = 0`.

## Main declarations

* `Fabius.canonicalBase_natCast_pos` — at `x = n` the base of the
  factor of index `m + 1 > n` is positive.
* `Fabius.canonicalRealFactor_natCast_pos` — hence so is that factor.
* `Fabius.tprod_canonicalRealFactor_add_pos_of` — a tail of the real
  canonical product is positive as soon as each of its factors is.
* `Fabius.neg_one_pow_mul_prod_range_natCast_pos` — **the new
  content**: at `x = n` with `m_a n = 0` the prefix `∏_{m<n}` carries
  the sign `(-1)^(∑_{m<n} m_a(m+1))`, the index `m + 1 = n`
  contributing the factor `1`.
* `Fabius.neg_one_pow_mul_canonicalRealProduct_natCast_pos` — the
  sign law at the integer point, with the prefix exponent.
* `Fabius.neg_one_pow_cumulative_mul_canonicalRealProduct_natCast_pos`
  — **`p1:eq:lobe-sign-count` at an integer point**, with the
  exponent in the volume's floor form `M_a(n)`.
* `Fabius.parityCharacter_mul_canonicalRealProduct_natCast_pos` —
  **`p1:eq:sign-master` at an integer point**, as an inequality.
* `Fabius.canonicalRealProduct_natCast_eq_parityCharacter_mul_abs` —
  the same law in `sign · absolute value` form.
* `Fabius.generalizedRvachevProduct_natCast_eq_parityCharacter_mul_norm`
  — the master law at an integer point, on `Φ_a` itself.
* `Fabius.generalizedRvachevProduct_natCast_eq_zero_of_ne_zero` — the
  converse half of the hypothesis, quoted from
  `Fabius.generalizedRvachevProduct_eq_zero_iff`: a nonzero
  multiplicity really does make `Φ_a(n) = 0`.
* `Fabius.canonicalRealProduct_deltaOneExponent_one_pos`,
  `Fabius.canonicalRealProduct_deltaOneExponent_three_neg` —
  **numeric guards** at `δ₁`, whose odd multiplicities vanish.
* `Fabius.canonicalComplexFactor` — the canonical factor over `ℂ`.
* `Fabius.canonicalComplexFactor_neg` — it is even in `z`.
* `Fabius.generalizedRvachevProduct_eq_tprod_canonicalComplexFactor` —
  the canonical form of `GeneralizedCanonicalForm`, in that notation.
* `Fabius.summable_norm_canonicalComplexFactor_sub_one` — the factor
  deviations are absolutely summable over `ℂ`.
* `Fabius.multipliable_canonicalComplexFactor` — the complex family is
  `Multipliable`.
* `Fabius.multipliable_update_canonicalComplexFactor` — so is the
  family with the index `m` replaced by `1`.
* `Fabius.canonicalCofactor` — **`R_n`**, the product of all canonical
  factors except the one of index `n = m + 1`.
* `Fabius.canonicalCofactor_neg` — `R_n` is even in `z`.
* `Fabius.generalizedRvachevProduct_eq_canonicalComplexFactor_mul` —
  **the factorization** `Φ_a(z) = (1 - z²/n²)^(m_a n) · R_n(z)`.
* `Fabius.canonicalCofactor_ne_zero` — `R_n(z) ≠ 0` whenever no other
  canonical base vanishes at `z`.
* `Fabius.canonicalCofactor_natCast_ne_zero`,
  `Fabius.canonicalCofactor_neg_natCast_ne_zero` — **`R_n(±n) ≠ 0`**.
* `Fabius.generalizedRvachevProduct_natCast_ne_zero_of_eq_zero` — the
  two parts meet: a zero multiplicity makes `Φ_a(n) ≠ 0`, over `ℂ`.
* `Fabius.canonicalRealProduct_zero_eq_one` — the residue at `x = 0`,
  which the integer-point hypothesis does not reach.
* `Fabius.analyticOrderAt_generalizedRvachevProduct_one` — the
  volume's `ord_{z=±n} Φ_a = m_a(n)` at the constant weight, the one
  case in which the corpus supplies analyticity.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Part one: the sign of the canonical product at an integer -/

/-- **The positive factors at an integer point.**  If `n ≤ m` — that
is, the index `n' = m + 1` of the factor exceeds the point `n` — then
the base of the `m`-th canonical factor at `x = n` is positive.

This is `Fabius.canonicalBase_pos` with the lobe hypothesis
`N < x < N + 1` replaced by the integer point `x = N`, which that
lemma excludes. -/
theorem canonicalBase_natCast_pos {n m : ℕ} (hm : n ≤ m) :
    0 < 1 - (n : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
  have hx0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlt : (n : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    have hn : n < m + 1 := by omega
    exact_mod_cast hn
  have hmp : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hden : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := pow_pos hmp 2
  have hsq : (n : ℝ) ^ 2 < ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_lt_mul_self hx0 hlt
  have hlt1 := (div_lt_one hden).mpr hsq
  linarith

/-- A positive base raised to any natural exponent stays positive, so
at `x = n` every canonical factor of index above `n` is positive. -/
theorem canonicalRealFactor_natCast_pos (a : ℕ → ℕ) {n m : ℕ}
    (hm : n ≤ m) : 0 < canonicalRealFactor a (n : ℝ) m := by
  rw [canonicalRealFactor]
  exact pow_pos (canonicalBase_natCast_pos hm) _

/-- **A positive tail.**  If every factor of the tail beyond the cut
`N` is positive then so is the tail, because the deviations are
summable, hence the logarithms are summable, and the tail is the
exponential of their sum (`Real.rexp_tsum_eq_tprod`).

This is `Fabius.tprod_canonicalRealFactor_add_pos` with the lobe
hypothesis replaced by the pointwise positivity that it derived from
the lobe; stated this way it also serves the integer point. -/
theorem tprod_canonicalRealFactor_add_pos_of (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) (N : ℕ)
    (hpos : ∀ m : ℕ, 0 < canonicalRealFactor a x (m + N)) :
    0 < ∏' m : ℕ, canonicalRealFactor a x (m + N) := by
  have hdev : Summable fun m : ℕ =>
      canonicalRealFactor a x (m + N) - 1 :=
    (summable_nat_add_iff
      (f := fun m : ℕ => canonicalRealFactor a x m - 1) N).mpr
      (summable_canonicalRealFactor_sub_one a ha x)
  have hlog0 : Summable fun m : ℕ =>
      Real.log (1 + (canonicalRealFactor a x (m + N) - 1)) :=
    Real.summable_log_one_add_of_summable hdev
  have hlog : Summable fun m : ℕ =>
      Real.log (canonicalRealFactor a x (m + N)) :=
    hlog0.congr fun m => congrArg Real.log (by ring)
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

/-- **The prefix at an integer point, and the whole new content of
part one.**  At `x = n`, under `m_a n = 0`,

`0 < (-1)^(∑_{m<n} m_a(m+1)) · ∏_{m<n} factor m`.

Two kinds of index occur in the prefix.  For `m + 1 < n` the base is
negative, exactly as on a lobe, and the factor is `(-1)^(m_a(m+1))`
times a positive number.  For `m + 1 = n` the base is `0`, which is
*not* negative; but the hypothesis makes its exponent `0`, so the
factor is `0 ^ 0 = 1`, and `1 = (-1)^0 · |0|^0` keeps the same
bookkeeping.  This is why the exponent `∑_{m<n} m_a(m+1)` may include
the term `m = n - 1` without changing the sign. -/
theorem neg_one_pow_mul_prod_range_natCast_pos (a : ℕ → ℕ) {n : ℕ}
    (hz : weightedScaleMultiplicity 2 a n = 0) :
    0 < (-1 : ℝ) ^
        (∑ m ∈ range n, weightedScaleMultiplicity 2 a (m + 1)) *
      ∏ m ∈ range n, canonicalRealFactor a (n : ℝ) m := by
  have hfac : ∀ m ∈ range n, canonicalRealFactor a (n : ℝ) m =
      (-1 : ℝ) ^ weightedScaleMultiplicity 2 a (m + 1) *
        |1 - (n : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2| ^
          weightedScaleMultiplicity 2 a (m + 1) := by
    intro m hm
    rcases eq_or_ne (m + 1) n with heq | hne
    · have he : weightedScaleMultiplicity 2 a (m + 1) = 0 := by
        rw [heq]
        exact hz
      rw [canonicalRealFactor, he]
      simp only [pow_zero, one_mul]
    · have hmn : ((m + 1 : ℕ) : ℝ) < (n : ℝ) := by
        have h1 := Finset.mem_range.mp hm
        have h2 : m + 1 < n := by omega
        exact_mod_cast h2
      have hneg : 1 - (n : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 < 0 :=
        canonicalBase_neg hmn (by omega)
      have hb : (-1 : ℝ) * |1 - (n : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2|
          = 1 - (n : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        rw [abs_of_neg hneg]
        ring
      rw [canonicalRealFactor]
      conv_lhs => rw [← hb]
      rw [mul_pow]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum (range n)
      (fun m => weightedScaleMultiplicity 2 a (m + 1)) (-1 : ℝ),
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]
  refine Finset.prod_pos fun m hm => ?_
  rcases eq_or_ne (m + 1) n with heq | hne
  · have he : weightedScaleMultiplicity 2 a (m + 1) = 0 := by
      rw [heq]
      exact hz
    rw [he, pow_zero]
    exact one_pos
  · have hmn : ((m + 1 : ℕ) : ℝ) < (n : ℝ) := by
      have h1 := Finset.mem_range.mp hm
      have h2 : m + 1 < n := by omega
      exact_mod_cast h2
    have hneg : 1 - (n : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 < 0 :=
      canonicalBase_neg hmn (by omega)
    exact pow_pos (abs_pos.mpr (ne_of_lt hneg)) _

/-- **The sign law at an integer point, with the prefix exponent.**
If `m_a n = 0` then

`0 < (-1)^(∑_{m<n} m_a(m+1)) · Ψ_a(n)`.

The split is the one of `Fabius.canonicalRealProduct_eq_prod_mul_tprod`
at the cut `n`; the prefix carries that sign and the tail is
positive.  At `n = 0` both blocks are trivial: the prefix is empty and
the tail has every base `1`. -/
theorem neg_one_pow_mul_canonicalRealProduct_natCast_pos (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {n : ℕ}
    (hz : weightedScaleMultiplicity 2 a n = 0) :
    0 < (-1 : ℝ) ^
        (∑ m ∈ range n, weightedScaleMultiplicity 2 a (m + 1)) *
      canonicalRealProduct a (n : ℝ) := by
  rw [canonicalRealProduct_eq_prod_mul_tprod a ha (n : ℝ) n,
    ← mul_assoc]
  refine mul_pos (neg_one_pow_mul_prod_range_natCast_pos a hz) ?_
  exact tprod_canonicalRealFactor_add_pos_of a ha (n : ℝ) n
    (fun m => canonicalRealFactor_natCast_pos a (Nat.le_add_left n m))

/-- **`p1:eq:lobe-sign-count` at an integer point.**  If `m_a n = 0`
then

`0 < (-1)^(M_a(n)) · Ψ_a(n)`,  `M_a(n) = ∑_{h<n} ⌊n/2^h⌋·a_h`.

The two exponents agree by
`Fabius.sum_range_weightedScaleMultiplicity`, exactly as in the
open-lobe case. -/
theorem neg_one_pow_cumulative_mul_canonicalRealProduct_natCast_pos
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hz : weightedScaleMultiplicity 2 a n = 0) :
    0 < (-1 : ℝ) ^ (∑ h ∈ range n, n / 2 ^ h * a h) *
      canonicalRealProduct a (n : ℝ) := by
  have hM : ∑ m ∈ range n, weightedScaleMultiplicity 2 a (m + 1)
      = ∑ h ∈ range n, n / 2 ^ h * a h := by
    rw [sum_range_weightedScaleMultiplicity 2 n a (by norm_num)]
    simp only [Nat.nsmul_eq_mul]
  rw [← hM]
  exact neg_one_pow_mul_canonicalRealProduct_natCast_pos a ha hz

/-- **`p1:eq:sign-master` at an integer point, as an inequality.**  If
`m_a n = 0` then

`0 < ε_a(n) · Ψ_a(n)`,

the *same* formula the volume states on the lobes.  Together with
`Fabius.parityCharacter_mul_canonicalRealProduct_pos` this covers
every real `x > 0` at which no factor of `Φ_a` vanishes.  The volume
phrases its law "away from the integer zeros"; `x = 0` and the
negative axis are discussed in the module header. -/
theorem parityCharacter_mul_canonicalRealProduct_natCast_pos
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hz : weightedScaleMultiplicity 2 a n = 0) :
    0 < ((parityCharacter a n : ℤ) : ℝ) *
      canonicalRealProduct a (n : ℝ) := by
  have hchar : ((parityCharacter a n : ℤ) : ℝ)
      = (-1 : ℝ) ^ (∑ h ∈ range n, n / 2 ^ h * a h) := by
    rw [← neg_one_pow_sum_div_two_pow a Nat.lt_two_pow_self]
    push_cast
    try ring
  rw [hchar]
  exact neg_one_pow_cumulative_mul_canonicalRealProduct_natCast_pos
    a ha hz

/-- **`p1:eq:sign-master` at an integer point, in
`sign · absolute value` form.**  If `m_a n = 0` then

`Ψ_a(n) = ε_a(n) · |Ψ_a(n)|`. -/
theorem canonicalRealProduct_natCast_eq_parityCharacter_mul_abs
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hz : weightedScaleMultiplicity 2 a n = 0) :
    canonicalRealProduct a (n : ℝ) =
      ((parityCharacter a n : ℤ) : ℝ) *
        |canonicalRealProduct a (n : ℝ)| := by
  have hpos :=
    parityCharacter_mul_canonicalRealProduct_natCast_pos a ha hz
  have hpm : parityCharacter a n = 1 ∨ parityCharacter a n = -1 := by
    rcases Nat.even_or_odd (∑ h ∈ bitSupport n, a h) with he | ho
    · refine Or.inl ?_
      show (-1 : ℤ) ^ (∑ h ∈ bitSupport n, a h) = 1
      exact he.neg_one_pow
    · refine Or.inr ?_
      show (-1 : ℤ) ^ (∑ h ∈ bitSupport n, a h) = -1
      exact ho.neg_one_pow
  rcases hpm with h1 | h1
  · have hcast : ((parityCharacter a n : ℤ) : ℝ) = 1 := by
      rw [h1]
      norm_num
    rw [hcast, one_mul] at hpos
    rw [hcast, one_mul, abs_of_pos hpos]
  · have hcast : ((parityCharacter a n : ℤ) : ℝ) = -1 := by
      rw [h1]
      norm_num
    rw [hcast] at hpos
    have hP : canonicalRealProduct a (n : ℝ) < 0 := by linarith
    rw [hcast, abs_of_neg hP]
    ring

/-- **The master law at an integer point, on the transform itself.**
If `m_a n = 0` then

`Φ_a(n) = ε_a(n) · ‖Φ_a(n)‖`,

a real number whose sign is the weighted parity character of `n`.
The transport is the bridge
`Fabius.generalizedRvachevProduct_ofReal_eq_canonicalRealProduct`,
read at the real point `(n : ℝ)`. -/
theorem generalizedRvachevProduct_natCast_eq_parityCharacter_mul_norm
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hz : weightedScaleMultiplicity 2 a n = 0) :
    generalizedRvachevProduct a ((n : ℕ) : ℂ) =
      ((((parityCharacter a n : ℤ) : ℝ) *
        ‖generalizedRvachevProduct a ((n : ℕ) : ℂ)‖ : ℝ) : ℂ) := by
  have hb := generalizedRvachevProduct_ofReal_eq_canonicalRealProduct
    a ha ((n : ℕ) : ℝ)
  rw [Complex.ofReal_natCast] at hb
  rw [hb, Complex.norm_real, Real.norm_eq_abs]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (canonicalRealProduct_natCast_eq_parityCharacter_mul_abs a ha hz)

/-- **The converse half of the hypothesis**, quoted rather than
reproved.  If `n ≥ 1` and `m_a n ≠ 0` then `Φ_a(n) = 0`.

`m_a n = ∑_{h ≤ v₂ n} a_h` is a sum of natural numbers, so a nonzero
value produces some `h ≤ v₂ n` with `a h ≠ 0`; then `2 ^ h ∣ n`, so
`n = k · 2 ^ h` with `k ≥ 1`, which is precisely the right-hand side
of the corpus's zero-set description
`Fabius.generalizedRvachevProduct_eq_zero_iff`.

So the hypothesis `m_a n = 0` of the sign law above is not a
convenience: outside it the value is `0` and has no sign. -/
theorem generalizedRvachevProduct_natCast_eq_zero_of_ne_zero
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hn : n ≠ 0)
    (hz : weightedScaleMultiplicity 2 a n ≠ 0) :
    generalizedRvachevProduct a ((n : ℕ) : ℂ) = 0 := by
  rw [weightedScaleMultiplicity, inclusivePrefixSum] at hz
  have hex : ∃ h ∈ range (padicValNat 2 n + 1), a h ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (Finset.sum_eq_zero hcon)
  obtain ⟨h, hh, hah⟩ := hex
  have hle : h ≤ padicValNat 2 n :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  have hdvd : 2 ^ h ∣ n :=
    dvd_trans (pow_dvd_pow 2 hle) pow_padicValNat_dvd
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hk
    exact hn hk
  refine (generalizedRvachevProduct_eq_zero_iff a ha _).mpr ?_
  refine ⟨h, hah, (k : ℤ), by exact_mod_cast hk0, ?_⟩
  rw [hk]
  push_cast
  try ring

/-- `δ₁` has a zero layer at height `0`, so every odd index has
multiplicity `m_{δ₁}(n) = δ₁(0) = 0`: the transform `sinc (z/2)` does
not vanish at any odd integer. -/
private theorem weightedScaleMultiplicity_deltaOne_odd {n : ℕ}
    (hn : ¬ (2 ∣ n)) :
    weightedScaleMultiplicity 2 deltaOneExponent n = 0 := by
  have hv : padicValNat 2 n = 0 :=
    padicValNat.eq_zero_of_not_dvd hn
  have h1 : deltaOneExponent 0 = 0 := by decide
  rw [weightedScaleMultiplicity, hv, inclusivePrefixSum_zero, h1]

/-- **Numeric guard, positive integer point.**  At `n = 1` the
cumulative count for `δ₁` is `⌊1/2^0⌋·δ₁(0) = 0`, an even number, so
`Ψ_{δ₁}(1) > 0`.  Checked numerically first: `Φ_{δ₁}(1) = sinc(1/2)`,
which is `2/π = 0.63662…`.  The index `m = 0` of this instance is
exactly the new case — its base is `1 - 1/1 = 0` and its exponent is
`0`, so it contributes the factor `1`. -/
theorem canonicalRealProduct_deltaOneExponent_one_pos :
    0 < canonicalRealProduct deltaOneExponent 1 := by
  have hz : weightedScaleMultiplicity 2 deltaOneExponent 1 = 0 :=
    weightedScaleMultiplicity_deltaOne_odd (by decide)
  have h :=
    neg_one_pow_cumulative_mul_canonicalRealProduct_natCast_pos
      deltaOneExponent summable_deltaOneExponent hz
  have hexp : ∑ h ∈ range 1, 1 / 2 ^ h * deltaOneExponent h = 0 := by
    norm_num [Finset.sum_range_succ, deltaOneExponent]
  have hcast : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
  rw [hexp, pow_zero, one_mul, hcast] at h
  exact h

/-- **Numeric guard, negative integer point.**  At `n = 3` the
cumulative count for `δ₁` is
`⌊3/2^0⌋·δ₁(0) + ⌊3/2^1⌋·δ₁(1) + ⌊3/2^2⌋·δ₁(2) = 1`, an odd number,
so `Ψ_{δ₁}(3) < 0`.  Checked numerically first:
`Φ_{δ₁}(3) = sinc(3/2) = -2/(3π) = -0.21221…`.  A flipped sign
convention would have to survive both this guard and the positive one
above. -/
theorem canonicalRealProduct_deltaOneExponent_three_neg :
    canonicalRealProduct deltaOneExponent 3 < 0 := by
  have hz : weightedScaleMultiplicity 2 deltaOneExponent 3 = 0 :=
    weightedScaleMultiplicity_deltaOne_odd (by decide)
  have h :=
    neg_one_pow_cumulative_mul_canonicalRealProduct_natCast_pos
      deltaOneExponent summable_deltaOneExponent hz
  have hexp : ∑ h ∈ range 3, 3 / 2 ^ h * deltaOneExponent h = 1 := by
    norm_num [Finset.sum_range_succ, deltaOneExponent]
  have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  rw [hexp, pow_one, hcast] at h
  linarith

/-! ## Part two: the factored form at one index -/

/-- The canonical factor of index `m`, that is, of the positive
integer `n = m + 1`, over `ℂ`:

`(1 - z²/(m+1)²) ^ (weightedScaleMultiplicity 2 a (m+1))`.

This is the body of the product in
`Fabius.generalizedRvachevProduct_eq_canonical`, named so that a
single index can be separated from it.  The exponent is the volume's
`m_a(n)`; nothing here asserts that it is an order of vanishing. -/
noncomputable def canonicalComplexFactor (a : ℕ → ℕ) (z : ℂ)
    (m : ℕ) : ℂ :=
  (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^
    weightedScaleMultiplicity 2 a (m + 1)

/-- Every canonical factor is an even function of `z`, since only
`z ^ 2` occurs.  This is what makes the statement at `-n` a corollary
of the statement at `n`. -/
theorem canonicalComplexFactor_neg (a : ℕ → ℕ) (z : ℂ) (m : ℕ) :
    canonicalComplexFactor a (-z) m = canonicalComplexFactor a z m := by
  rw [canonicalComplexFactor, canonicalComplexFactor, neg_sq]

/-- The canonical form of
`Fabius.generalizedRvachevProduct_eq_canonical` written with
`canonicalComplexFactor`:

`Φ_a(z) = ∏'_m canonicalComplexFactor a z m`.

The two sides are definitionally equal; this lemma only fixes the
notation used in the rest of the file. -/
theorem generalizedRvachevProduct_eq_tprod_canonicalComplexFactor
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    generalizedRvachevProduct a z =
      ∏' m : ℕ, canonicalComplexFactor a z m :=
  generalizedRvachevProduct_eq_canonical a ha z

/-- **Absolute summability of the complex factor deviations.**  Under
admissibility,

`∑_m ‖(1 - z²/(m+1)²)^(m_a(m+1)) - 1‖ < ∞`.

This is the complex form of
`Fabius.summable_canonicalRealFactor_sub_one`, and the proof is the
same two steps: the power deviation bound
`Fabius.norm_one_add_pow_sub_one_le` turns the `m`-th summand into
`exp (m_a(m+1)·‖z‖²/(m+1)²) - 1`, and the series in the exponent is
`‖z‖²` times the spectral zeta series at `s = 2`
(`Fabius.summable_weightedScaleMultiplicity_div_sq`). -/
theorem summable_norm_canonicalComplexFactor_sub_one (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) :
    Summable fun m : ℕ => ‖canonicalComplexFactor a z m - 1‖ := by
  have hv : Summable fun m : ℕ =>
      ‖z‖ ^ 2 * (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
        / ((m + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_weightedScaleMultiplicity_div_sq a ha).mul_left (‖z‖ ^ 2)
  have h0 : ∀ m : ℕ, (0 : ℝ) ≤
      ‖z‖ ^ 2 * (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
        / ((m + 1 : ℕ) : ℝ) ^ 2) := by
    intro m
    positivity
  refine summable_norm_of_norm_le_exp_sub_one hv h0 ?_
  intro m
  have hy : ‖(-(z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2))‖
      = ‖z‖ ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_neg, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hb := norm_one_add_pow_sub_one_le
    (-(z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2))
    (weightedScaleMultiplicity 2 a (m + 1))
  rw [hy] at hb
  have h1 : (1 : ℂ) + -(z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2)
      = 1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by ring
  have h2 : ((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
        * (‖z‖ ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2)
      = ‖z‖ ^ 2 * (((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℝ)
          / ((m + 1 : ℕ) : ℝ) ^ 2) := by ring
  rw [h1, h2] at hb
  simpa only [canonicalComplexFactor] using hb

/-- **The complex family is `Multipliable`.**  Its deviations from `1`
are absolutely summable, which is the hypothesis of Mathlib's
`multipliable_one_add_of_summable` in a complete normed commutative
ring.  No hypothesis on `z` is needed: at a zero a factor simply
vanishes, and Mathlib's `Multipliable` admits the limit `0`. -/
theorem multipliable_canonicalComplexFactor (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) :
    Multipliable (canonicalComplexFactor a z) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_canonicalComplexFactor_sub_one a ha z)
  exact h.congr fun m => by ring

/-- The family with the index `m` overwritten by `1` is `Multipliable`
too: overwriting one term can only shrink a deviation.

This is the exact convergence hypothesis of Mathlib's
`Multipliable.tprod_eq_mul_tprod_ite'`, the `CommMonoid` form of the
single-index split.  The `CommGroup` form
`Multipliable.tprod_eq_mul_tprod_ite`, which would need no such
hypothesis, does not apply: `ℂ` is not a topological group under
multiplication. -/
theorem multipliable_update_canonicalComplexFactor (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) (m : ℕ) :
    Multipliable
      (Function.update (canonicalComplexFactor a z) m 1) := by
  have hsum : Summable fun k : ℕ =>
      ‖Function.update (canonicalComplexFactor a z) m 1 k - 1‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_
      (summable_norm_canonicalComplexFactor_sub_one a ha z)
    intro k
    by_cases hk : k = m
    · rw [hk, Function.update_self, sub_self, norm_zero]
      exact norm_nonneg _
    · exact le_of_eq (by rw [Function.update_of_ne hk])
  have h := multipliable_one_add_of_summable hsum
  exact h.congr fun k => by ring

/-- **`R_n`, the complementary factor** at the index `n = m + 1`: the
product of every canonical factor except the one of index `m`,

`R_n(z) = ∏'_{k ≠ m} (1 - z²/(k+1)²) ^ (m_a(k+1))`.

The excluded index is written as the value `1` at `k = m` rather than
as a product over a subtype, which is the shape Mathlib's
single-index split produces. -/
noncomputable def canonicalCofactor (a : ℕ → ℕ) (m : ℕ) (z : ℂ) : ℂ :=
  ∏' k : ℕ, if k = m then 1 else canonicalComplexFactor a z k

/-- `R_n` is an even function of `z`, because every canonical factor
is. -/
theorem canonicalCofactor_neg (a : ℕ → ℕ) (m : ℕ) (z : ℂ) :
    canonicalCofactor a m (-z) = canonicalCofactor a m z := by
  rw [canonicalCofactor, canonicalCofactor]
  refine tprod_congr fun k => ?_
  by_cases hk : k = m
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, canonicalComplexFactor_neg]

/-- **The factored form at one index.**  For `n = m + 1 ≥ 1` and every
`z : ℂ`,

`Φ_a(z) = (1 - z²/n²) ^ (m_a n) · R_n(z)`.

This is the canonical product of
`Fabius.generalizedRvachevProduct_eq_canonical` split at the single
index `m` by Mathlib's `Multipliable.tprod_eq_mul_tprod_ite'`.

**It is not an order-of-vanishing statement.**  Together with
`canonicalCofactor_natCast_ne_zero` below it is the algebraic input to
one: it exhibits `(1 - z²/n²)^(m_a n)` as a factor and shows that
what remains does not vanish at `±n`.  Converting that into
`ord_{z=±n} Φ_a = m_a(n)` needs `R_n` to be analytic near `±n`, hence
needs convergence of the canonical product uniform on compact sets,
which the corpus does not have. -/
theorem generalizedRvachevProduct_eq_canonicalComplexFactor_mul
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (m : ℕ) (z : ℂ) :
    generalizedRvachevProduct a z =
      canonicalComplexFactor a z m * canonicalCofactor a m z := by
  rw [generalizedRvachevProduct_eq_tprod_canonicalComplexFactor a ha z,
    canonicalCofactor]
  exact Multipliable.tprod_eq_mul_tprod_ite' m
    (multipliable_update_canonicalComplexFactor a ha z m)

/-- **The complementary factor does not vanish** at any point where no
*other* canonical base vanishes.

This is where the content of part two sits.  Each surviving factor is
a power of a nonzero base, hence nonzero, and the infinite product of
them cannot conspire to reach `0` because the deviations are
absolutely summable — the hypothesis of Mathlib's
`tprod_one_add_ne_zero_of_summable`.  The argument is the one the
corpus already runs in `Fabius.generalizedRvachevProduct_ne_zero`, on
the scale factors instead of the canonical ones. -/
theorem canonicalCofactor_ne_zero (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (m : ℕ) {z : ℂ}
    (hz : ∀ k : ℕ, k ≠ m →
      1 - z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2 ≠ 0) :
    canonicalCofactor a m z ≠ 0 := by
  have hsum : Summable fun k : ℕ =>
      ‖(if k = m then (1 : ℂ) else canonicalComplexFactor a z k)
        - 1‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_
      (summable_norm_canonicalComplexFactor_sub_one a ha z)
    intro k
    by_cases hk : k = m
    · rw [if_pos hk, sub_self, norm_zero]
      exact norm_nonneg _
    · exact le_of_eq (by rw [if_neg hk])
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun k : ℕ =>
      (if k = m then (1 : ℂ) else canonicalComplexFactor a z k) - 1)
    (fun k => by
      have hx : (1 : ℂ) +
          ((if k = m then (1 : ℂ) else canonicalComplexFactor a z k)
            - 1)
          = if k = m then (1 : ℂ)
              else canonicalComplexFactor a z k := by ring
      rw [hx]
      by_cases hk : k = m
      · rw [if_pos hk]
        exact one_ne_zero
      · rw [if_neg hk, canonicalComplexFactor]
        exact pow_ne_zero _ (hz k hk)) hsum
  have hbody : (fun k : ℕ => (1 : ℂ) +
      ((if k = m then (1 : ℂ) else canonicalComplexFactor a z k) - 1))
      = fun k : ℕ =>
        if k = m then (1 : ℂ) else canonicalComplexFactor a z k := by
    funext k
    ring
  rw [canonicalCofactor]
  rwa [hbody] at h

/-- **`R_n(n) ≠ 0`.**  At `z = n = m + 1` the base of the factor of
index `k ≠ m` is `1 - n²/(k+1)²`, and
`Fabius.canonicalFactor_eq_zero_iff` says it vanishes only at
`z = ±(k+1)`.  The first alternative forces `m + 1 = k + 1`, excluded;
the second forces `(m+1) + (k+1) = 0` in `ℕ`, impossible. -/
theorem canonicalCofactor_natCast_ne_zero (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (m : ℕ) :
    canonicalCofactor a m ((m + 1 : ℕ) : ℂ) ≠ 0 := by
  refine canonicalCofactor_ne_zero a ha m ?_
  intro k hk hzero
  rcases (canonicalFactor_eq_zero_iff k ((m + 1 : ℕ) : ℂ)).mp hzero
    with h1 | h1
  · have h2 : m + 1 = k + 1 := Nat.cast_inj.mp h1
    exact hk (by omega)
  · have h2 : (((m + 1) + (k + 1) : ℕ) : ℂ) = 0 := by
      push_cast at h1 ⊢
      linear_combination h1
    have h3 : (m + 1) + (k + 1) = 0 := by exact_mod_cast h2
    omega

/-- **`R_n(-n) ≠ 0`**, by evenness of the complementary factor. -/
theorem canonicalCofactor_neg_natCast_ne_zero (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (m : ℕ) :
    canonicalCofactor a m (-((m + 1 : ℕ) : ℂ)) ≠ 0 := by
  rw [canonicalCofactor_neg]
  exact canonicalCofactor_natCast_ne_zero a ha m

/-- **The two parts meet.**  If `m_a(m+1) = 0` then the factored form
reads `Φ_a(m+1) = 1 · R_{m+1}(m+1)`, so `Φ_a(m+1) ≠ 0`, over `ℂ`.

Part one gets the same nonvanishing over `ℝ` as a by-product of the
sign law; here it comes from the factorization instead, so the two
routes to "an integer with a zero layer is not a zero of `Φ_a`" agree.
Combined with
`Fabius.generalizedRvachevProduct_natCast_eq_zero_of_ne_zero` this
determines the zero set of `Φ_a` on the positive integers exactly:
`Φ_a(n) = 0` if and only if `m_a n ≠ 0`. -/
theorem generalizedRvachevProduct_natCast_ne_zero_of_eq_zero
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {m : ℕ} (hz : weightedScaleMultiplicity 2 a (m + 1) = 0) :
    generalizedRvachevProduct a ((m + 1 : ℕ) : ℂ) ≠ 0 := by
  rw [generalizedRvachevProduct_eq_canonicalComplexFactor_mul a ha m,
    canonicalComplexFactor, hz, pow_zero, one_mul]
  exact canonicalCofactor_natCast_ne_zero a ha m

/-- The residue at `x = 0`, which the hypothesis `m_a n = 0` of the
integer-point law does not reach: every canonical base is `1` there,
so the product is `1` and no factor vanishes whatever the weight. -/
theorem canonicalRealProduct_zero_eq_one (a : ℕ → ℕ) :
    canonicalRealProduct a 0 = 1 := by
  have hbase : ∀ m : ℕ, canonicalRealFactor a 0 m = 1 := by
    intro m
    rw [canonicalRealFactor]
    norm_num
  rw [canonicalRealProduct, tprod_congr hbase, tprod_one]

/-- **The volume's `ord_{z=±n} Φ_a = m_a(n)`, at the constant
weight.**  This is the one case in which the corpus has analyticity,
so it is the one case in which the order statement is available: it
chains `generalizedRvachevProduct_one` with the corpus's
`analyticOrderAt_rvachevFourierProduct_int` and the exponent identity
`weightedScaleMultiplicity_one_nat`.

For a general admissible `a` the corresponding statement is open; the
factorization above is its algebraic input. -/
theorem analyticOrderAt_generalizedRvachevProduct_one (m : ℤ)
    (hm : m ≠ 0) :
    analyticOrderAt (generalizedRvachevProduct (fun _ => 1))
        ((m : ℤ) : ℂ)
      = weightedScaleMultiplicity 2 (fun _ => 1) m.natAbs := by
  have hfun : generalizedRvachevProduct (fun _ => 1)
      = rvachevFourierProduct := by
    funext w
    exact generalizedRvachevProduct_one w
  rw [hfun, analyticOrderAt_rvachevFourierProduct_int m hm,
    weightedScaleMultiplicity_one_nat]

end Fabius
