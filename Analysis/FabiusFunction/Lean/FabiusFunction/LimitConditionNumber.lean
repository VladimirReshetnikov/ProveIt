import FabiusFunction.GeneralQConditionNumber
import FabiusFunction.WeierstrassProductBound
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The limiting condition number of the general-`q` Toeplitz rows

`GeneralQConditionNumber` evaluates the total variation of the `n`-th
general-`q` Fabius Toeplitz row in closed form: for `0 ≤ q < 1`,

`∑_{j≤n} |w_q(n,j)| = (-q;q)_n / (q;q)_n`.

This module lets `n` grow.  Both finite `q`-Pochhammer symbols are
partial products of families `j ↦ 1 - a q^j` whose deficits `a q^j`
are geometric, hence summable, so
`Real.multipliable_one_add_of_summable` makes both families
multipliable and the partial products converge to infinite products
`(a;q)_∞`.  The row is a quotient, so the limit of the quotient is
the quotient of the limits *provided the denominator limit is
nonzero*, and that is the whole difficulty.

The positivity of `(q;q)_∞` is **not** proved here through the
Weierstrass product inequality.  The one-shot bound is vacuous
beyond `q = 1/2`: the deficit budget is `∑_j q^{j+1} = q/(1-q)`,
computed inside `one_sub_geom_le_qPochhammerInf_self`, and it
already equals `1` at `q = 1/2`.  The theorem
`weierstrass_bound_vacuous_at_three_quarters` records that failure
at `q = 3/4` as a theorem rather than as prose; recovering the whole
range that way would still be possible, by peeling off a finite
prefix and applying the Weierstrass bound to the tail, whose deficit
`q^{N+1}/(1-q)` drops below `1` for large `N` at every `q < 1`.
Instead
positivity comes from `Real.rexp_tsum_eq_tprod`: the logarithms
`log (1 - a q^j)` are summable, so the infinite product is the
exponential of a real number and therefore strictly positive.  This
needs no threshold at all: the convergence and the positivity both
hold on the full range `0 ≤ q < 1`.  The Weierstrass bound is still
recorded, as the *effective* lower bound `1 - q/(1-q) ≤ (q;q)_∞`,
informative exactly when `q < 1/2`.

The limit is bounded below in two ways, and in no way from above --
it is unbounded as `q ↑ 1`.  It is at least `1`, that value being
attained exactly at `q = 0`; and it is at least `1/(1-q)`, a
consequence of the two-sided control of the *symbols*,
`(q;q)_∞ ≤ 1 - q` and `1 ≤ (-q;q)_∞`.  The second bound is strictly
above `1` as soon as `q > 0`, and at `q = 999/1000` it already
forces the limit to at least `1000`.

## Main declarations

* `qPochhammerInf` -- the infinite `q`-Pochhammer symbol `(a;q)_∞`,
  defined as `∏' j, (1 - a q^j)` over `ℝ`.
* `qPochhammerInf_eq_tprod` -- the definition, restated.
* `finiteQPochhammerIn_eq_prod_range` -- the explicit identification
  of the finite symbol with the `n`-th `Finset.range` partial
  product, which is what makes the limit statement literal.
* `multipliable_one_sub_mul_pow` -- **both families are
  multipliable** for `0 ≤ q < 1`, at every coefficient `a`.
* `tendsto_finiteQPochhammerIn` -- **the finite symbols converge**
  to `(a;q)_∞`.
* `qPochhammerInf_pos` -- **strict positivity of an infinite
  `q`-Pochhammer symbol** whose factors are all positive; the crux,
  via the summability of the logarithms.
* `qPochhammerInf_self_pos`, `qPochhammerInf_neg_self_pos` -- the two
  specializations, `(q;q)_∞ > 0` and `(-q;q)_∞ > 0` on the whole
  range `0 ≤ q < 1`, with no threshold on `q`.
* `qPochhammerInf_zero_left` -- `(0;q)_∞ = 1` at every base.
* `qConditionNumberLimit` -- the limiting condition number
  `(-q;q)_∞ / (q;q)_∞`.
* `tendsto_sum_abs_qToeplitzWeight` -- **the headline theorem**: the
  general-`q` condition numbers converge to `qConditionNumberLimit`.
* `one_le_qConditionNumberLimit` and `qConditionNumberLimit_zero` --
  the limit is at least one, and the bound is attained at `q = 0`.
* `qPochhammerInf_self_le_one_sub`,
  `one_le_qPochhammerInf_neg_self` -- the two sandwiching bounds
  `(q;q)_∞ ≤ 1 - q` and `1 ≤ (-q;q)_∞`.
* `one_div_one_sub_le_qConditionNumberLimit` and
  `tendsto_qConditionNumberLimit_atTop_at_one_left` -- hence
  `1/(1-q)` is a lower bound and the limiting condition number tends
  to `+∞` as `q → 1⁻`.
* `one_lt_qConditionNumberLimit` -- the limit is strictly above one
  for `q > 0`, so the bound `1` is attained only at `q = 0`.
* `thousand_le_qConditionNumberLimit` -- a concrete consequence: at
  `q = 999/1000` the limiting condition number is at least `1000`.
* `one_sub_geom_le_qPochhammerInf_self` and
  `weierstrass_bound_vacuous_at_three_quarters` -- the effective
  Weierstrass lower bound, and the theorem that it says nothing at
  `q = 3/4`.
-/

set_option autoImplicit false

open Filter Topology

open scoped BigOperators

namespace Fabius

/-! ## The infinite `q`-Pochhammer symbol -/

/-- The infinite `q`-Pochhammer symbol `(a;q)_∞ = ∏_{j≥0} (1 - a q^j)`
over the reals.  For `0 ≤ q < 1` the defining product converges, by
`multipliable_one_sub_mul_pow`. -/
noncomputable def qPochhammerInf (a q : ℝ) : ℝ :=
  ∏' j : ℕ, (1 - a * q ^ j)

/-- The definition of `qPochhammerInf`, restated. -/
theorem qPochhammerInf_eq_tprod (a q : ℝ) :
    qPochhammerInf a q = ∏' j : ℕ, (1 - a * q ^ j) := rfl

/-- **The finite `q`-Pochhammer symbol is literally the partial
product.**  `Fabius.finiteQPochhammerIn a q n` is the product over
`Finset.range n` of the very family whose infinite product is
`qPochhammerInf a q`, so the convergence statement below is a
statement about the `n`-th partial products on the nose, with no
reindexing. -/
theorem finiteQPochhammerIn_eq_prod_range (a q : ℝ) (n : ℕ) :
    finiteQPochhammerIn a q n =
      ∏ j ∈ Finset.range n, (1 - a * q ^ j) := rfl

/-! ## Multipliability and convergence -/

/-- **Both `q`-Pochhammer families are multipliable** for
`0 ≤ q < 1`, at every coefficient `a`.  The factors are
`1 + (-a q^j)`, and the deficit family `-a q^j` is a constant
multiple of the geometric series `q^j`, hence summable, so
`Real.multipliable_one_add_of_summable` applies.  No sign condition
on `a` enters, which is why the same lemma serves both `(q;q)_∞` and
`(-q;q)_∞`. -/
theorem multipliable_one_sub_mul_pow (a : ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Multipliable fun j : ℕ => 1 - a * q ^ j := by
  have hgeom : Summable fun j : ℕ => q ^ j :=
    summable_geometric_of_lt_one hq0 hq1
  have hsum : Summable fun j : ℕ => -a * q ^ j := hgeom.mul_left (-a)
  exact (Real.multipliable_one_add_of_summable hsum).congr
    fun j => by ring

/-- **The finite `q`-Pochhammer symbols converge.**  For `0 ≤ q < 1`
the sequence `n ↦ (a;q)_n` tends to `(a;q)_∞`.  The proof is
`Multipliable.tendsto_prod_tprod_nat` applied to the family of
`finiteQPochhammerIn_eq_prod_range`. -/
theorem tendsto_finiteQPochhammerIn (a : ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Tendsto (fun n : ℕ => finiteQPochhammerIn a q n) atTop
      (nhds (qPochhammerInf a q)) :=
  (multipliable_one_sub_mul_pow a hq0 hq1).tendsto_prod_tprod_nat

/-! ## Strict positivity of the infinite product -/

/-- The logarithms of the factors `1 - a q^j` are summable for
`0 ≤ q < 1`.  This is `Real.summable_log_one_add_of_summable` applied
to the geometric family `-a q^j`; it needs no positivity of the
factors, because that lemma is unconditional. -/
private theorem summable_log_one_sub_mul_pow {a q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Summable fun j : ℕ => Real.log (1 - a * q ^ j) := by
  have hgeom : Summable fun j : ℕ => q ^ j :=
    summable_geometric_of_lt_one hq0 hq1
  have hsum : Summable fun j : ℕ => -a * q ^ j := hgeom.mul_left (-a)
  have h := Real.summable_log_one_add_of_summable hsum
  refine h.congr fun j => ?_
  show Real.log (1 + -a * q ^ j) = Real.log (1 - a * q ^ j)
  rw [show (1 : ℝ) + -a * q ^ j = 1 - a * q ^ j from by ring]

/-- **Strict positivity of an infinite `q`-Pochhammer symbol.**  If
`0 ≤ q < 1` and every factor `1 - a q^j` is strictly positive, then
`(a;q)_∞ > 0`.

This is the crux of the module, and it is deliberately *not* proved
by the Weierstrass product inequality, which says nothing once the
deficit budget `∑_j |a| q^j` reaches `1`.  Instead the logarithms of
the factors are summable, so `Real.rexp_tsum_eq_tprod` exhibits the
infinite product as `exp` of a real number.  Consequently no
threshold on `q` appears: the conclusion holds on the entire range
`0 ≤ q < 1`. -/
theorem qPochhammerInf_pos {a q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hpos : ∀ j : ℕ, 0 < 1 - a * q ^ j) :
    0 < qPochhammerInf a q := by
  have hlog : Summable fun j : ℕ => Real.log (1 - a * q ^ j) :=
    summable_log_one_sub_mul_pow hq0 hq1
  have hexp :
      Real.exp (∑' j : ℕ, Real.log (1 - a * q ^ j)) =
        ∏' j : ℕ, (1 - a * q ^ j) :=
    Real.rexp_tsum_eq_tprod hpos hlog
  show (0 : ℝ) < ∏' j : ℕ, (1 - a * q ^ j)
  rw [← hexp]
  exact Real.exp_pos _

/-- **`(q;q)_∞ > 0` for every `0 ≤ q < 1`.**  Each factor
`1 - q q^j` is positive because `q q^j ≤ q < 1`.  This is the
nonvanishing that makes the limiting condition number a genuine real
number, and it is the general-base counterpart of
`Fabius.finiteQPochhammerIn_self_pos`. -/
theorem qPochhammerInf_self_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < qPochhammerInf q q := by
  refine qPochhammerInf_pos hq0 hq1 fun j => ?_
  have hpow : q ^ j ≤ 1 := pow_le_one₀ hq0 hq1.le
  have hmul : q * q ^ j ≤ q := mul_le_of_le_one_right hq0 hpow
  linarith

/-- `(-q;q)_∞ > 0` for every `0 ≤ q < 1`: each factor is
`1 + q q^j ≥ 1`. -/
theorem qPochhammerInf_neg_self_pos {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    0 < qPochhammerInf (-q) q := by
  refine qPochhammerInf_pos hq0 hq1 fun j => ?_
  have hnn : (0 : ℝ) ≤ q * q ^ j := mul_nonneg hq0 (pow_nonneg hq0 j)
  rw [neg_mul, sub_neg_eq_add]
  linarith

/-- At `a = 0` every factor is `1`, so `(0;q)_∞ = 1` for every base
`q`.  This is the degenerate case behind `qConditionNumberLimit_zero`
below. -/
theorem qPochhammerInf_zero_left (q : ℝ) : qPochhammerInf 0 q = 1 := by
  show (∏' j : ℕ, (1 - 0 * q ^ j)) = 1
  simp only [zero_mul, sub_zero, tprod_one]

/-! ## Two-sided control of the two symbols -/

/-- **`1 ≤ (-q;q)_∞`** for `0 ≤ q < 1`: every finite subproduct of
the factors `1 + q q^j` is at least one, including the empty one, so
the bound passes to the infinite product with no eventual-index
argument. -/
theorem one_le_qPochhammerInf_neg_self {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    1 ≤ qPochhammerInf (-q) q := by
  refine le_hasProd_of_le_prod
    (multipliable_one_sub_mul_pow (-q) hq0 hq1).hasProd fun s => ?_
  refine Finset.one_le_prod fun j _ => ?_
  have hnn : (0 : ℝ) ≤ q * q ^ j := mul_nonneg hq0 (pow_nonneg hq0 j)
  show (1 : ℝ) ≤ 1 - -q * q ^ j
  rw [neg_mul, sub_neg_eq_add]
  linarith

/-- Every nonempty finite `(q;q)`-symbol is at most `1 - q`: peeling
the first factor leaves a product of numbers in `[0,1]`. -/
private theorem finiteQPochhammerIn_self_succ_le {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    finiteQPochhammerIn q q (n + 1) ≤ 1 - q := by
  have hle : ∀ k : ℕ, q * q ^ (k + 1) ≤ q := by
    intro k
    exact mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ q * q ^ (k + 1) :=
    fun k => mul_nonneg hq0 (pow_nonneg hq0 _)
  have hfac0 : ∀ k : ℕ, (0 : ℝ) ≤ 1 - q * q ^ (k + 1) :=
    fun k => by linarith [hle k]
  have hfac1 : ∀ k : ℕ, (1 : ℝ) - q * q ^ (k + 1) ≤ 1 :=
    fun k => by linarith [hnn k]
  have hP : (∏ k ∈ Finset.range n, (1 - q * q ^ (k + 1))) ≤ 1 :=
    Finset.prod_le_one (fun k _ => hfac0 k) (fun k _ => hfac1 k)
  have hq' : (0 : ℝ) ≤ 1 - q := by linarith
  rw [finiteQPochhammerIn, Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  calc
    (∏ k ∈ Finset.range n, (1 - q * q ^ (k + 1))) * (1 - q) ≤
        1 * (1 - q) := mul_le_mul_of_nonneg_right hP hq'
    _ = 1 - q := one_mul _

/-- **`(q;q)_∞ ≤ 1 - q`** for `0 ≤ q < 1`.  The empty partial
product is `1`, which exceeds `1 - q` as soon as `q > 0`, so the
bound has to be inherited from the partial products of index at least
one; that is why the proof shifts the sequence before passing to the
limit. -/
theorem qPochhammerInf_self_le_one_sub {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    qPochhammerInf q q ≤ 1 - q :=
  le_of_tendsto'
    ((Filter.tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_finiteQPochhammerIn q hq0 hq1))
    fun n => finiteQPochhammerIn_self_succ_le hq0 hq1 n

/-! ## The limiting condition number -/

/-- The limiting condition number of the general-`q` Fabius Toeplitz
rows, `(-q;q)_∞ / (q;q)_∞`.  By `tendsto_sum_abs_qToeplitzWeight` it
is the limit of the row total variations. -/
noncomputable def qConditionNumberLimit (q : ℝ) : ℝ :=
  qPochhammerInf (-q) q / qPochhammerInf q q

/-- **The general-`q` condition numbers converge.**  For `0 ≤ q < 1`,

`∑_{j≤n} |w_q(n,j)| → (-q;q)_∞ / (q;q)_∞  as  n → ∞`.

Each term is exactly `(-q;q)_n / (q;q)_n` by
`Fabius.sum_abs_qToeplitzWeight`; numerator and denominator converge
by `tendsto_finiteQPochhammerIn`, and the denominator limit is
nonzero by `qPochhammerInf_self_pos`, which is the only place the
crux is spent. -/
theorem tendsto_sum_abs_qToeplitzWeight {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Tendsto
      (fun n : ℕ =>
        ∑ j ∈ Finset.range (n + 1), |qToeplitzWeight q n j|)
      atTop (nhds (qConditionNumberLimit q)) := by
  have hnum := tendsto_finiteQPochhammerIn (-q) hq0 hq1
  have hden := tendsto_finiteQPochhammerIn q hq0 hq1
  have hne : qPochhammerInf q q ≠ 0 :=
    (qPochhammerInf_self_pos hq0 hq1).ne'
  have hdiv := hnum.div hden hne
  refine Filter.Tendsto.congr (fun n => ?_) hdiv
  rw [Pi.div_apply]
  exact (sum_abs_qToeplitzWeight hq0 hq1 n).symm

/-- **The limiting condition number is at least one.**  Every finite
row has total variation at least one, and a lower bound valid at
every index passes to the limit. -/
theorem one_le_qConditionNumberLimit {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    1 ≤ qConditionNumberLimit q :=
  ge_of_tendsto' (tendsto_sum_abs_qToeplitzWeight hq0 hq1)
    fun n => one_le_sum_abs_qToeplitzWeight hq0 hq1 n

/-- **The bound `1` is attained.**  At `q = 0` both infinite symbols
degenerate to `1`, so the limiting condition number is exactly `1`.
Together with `one_lt_qConditionNumberLimit` this shows that `q = 0`
is the only base at which the lower bound of
`one_le_qConditionNumberLimit` is reached. -/
theorem qConditionNumberLimit_zero : qConditionNumberLimit 0 = 1 := by
  show qPochhammerInf (-0) 0 / qPochhammerInf 0 0 = 1
  rw [neg_zero, qPochhammerInf_zero_left, div_one]

/-- **`1/(1-q)` is a lower bound for the limiting condition
number.**  It follows from the sandwich `(q;q)_∞ ≤ 1 - q` and
`1 ≤ (-q;q)_∞`.  It is what pushes the limit above `1000` at
`q = 999/1000`; see `thousand_le_qConditionNumberLimit`. -/
theorem one_div_one_sub_le_qConditionNumberLimit {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 / (1 - q) ≤ qConditionNumberLimit q := by
  have hD : 0 < qPochhammerInf q q := qPochhammerInf_self_pos hq0 hq1
  have hDle : qPochhammerInf q q ≤ 1 - q :=
    qPochhammerInf_self_le_one_sub hq0 hq1
  have hN : 1 ≤ qPochhammerInf (-q) q :=
    one_le_qPochhammerInf_neg_self hq0 hq1
  have hstep : 1 / (1 - q) ≤ 1 / qPochhammerInf q q :=
    one_div_le_one_div_of_le hD hDle
  have hnn : (0 : ℝ) ≤
      (qPochhammerInf (-q) q - 1) / qPochhammerInf q q :=
    div_nonneg (by linarith) hD.le
  have hsplit :
      (qPochhammerInf (-q) q - 1) / qPochhammerInf q q =
        qPochhammerInf (-q) q / qPochhammerInf q q -
          1 / qPochhammerInf q q :=
    sub_div _ _ _
  rw [hsplit] at hnn
  show 1 / (1 - q) ≤ qPochhammerInf (-q) q / qPochhammerInf q q
  linarith

/-- **The limiting condition number diverges as `q → 1⁻`.**  The
pointwise lower bound `1 / (1 - q) ≤ qConditionNumberLimit q` is now
promoted to the literal filter statement

`qConditionNumberLimit q → +∞` as `q → 1` through values below one.

The proof needs no asymptotic information about either infinite product:
reflection sends the left neighborhood of `1` to the right neighborhood
of `0`, inversion sends that to `atTop`, and the established lower bound
finishes by eventual comparison. -/
theorem tendsto_qConditionNumberLimit_atTop_at_one_left :
    Tendsto qConditionNumberLimit (𝓝[<] (1 : ℝ)) atTop := by
  have hsub :
      Tendsto (fun q : ℝ => 1 - q) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcontinuous : Continuous (fun q : ℝ => 1 - q) := by fun_prop
      have hat : Tendsto (fun q : ℝ => 1 - q) (nhds (1 : ℝ))
          (nhds (1 - (1 : ℝ))) := hcontinuous.continuousAt
      simpa only [sub_self] using hat.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      change 0 < 1 - q
      exact sub_pos.mpr hq
  have hinv :
      Tendsto (fun q : ℝ => (1 - q)⁻¹) (𝓝[<] (1 : ℝ)) atTop :=
    hsub.inv_tendsto_nhdsGT_zero
  refine tendsto_atTop_mono' _ ?_ hinv
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with q hq1 hq0
  simpa only [one_div] using
    (one_div_one_sub_le_qConditionNumberLimit hq0.le hq1)

/-- **Strictness away from `q = 0`.**  For `0 < q < 1` the limiting
condition number is strictly above one, because `(q;q)_∞ ≤ 1 - q < 1`
while `(-q;q)_∞ ≥ 1`.  So `one_le_qConditionNumberLimit` is an
equality only at the base `q = 0`. -/
theorem one_lt_qConditionNumberLimit {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) :
    1 < qConditionNumberLimit q := by
  have hD : 0 < qPochhammerInf q q :=
    qPochhammerInf_self_pos hq0.le hq1
  have hDle : qPochhammerInf q q ≤ 1 - q :=
    qPochhammerInf_self_le_one_sub hq0.le hq1
  have hN : 1 ≤ qPochhammerInf (-q) q :=
    one_le_qPochhammerInf_neg_self hq0.le hq1
  have hlt : qPochhammerInf q q < qPochhammerInf (-q) q := by
    linarith
  show 1 < qPochhammerInf (-q) q / qPochhammerInf q q
  exact (one_lt_div hD).mpr hlt

/-- **A concrete large value.**  At `q = 999/1000` the lower bound
`1/(1-q)` reads `1000`, so the limiting condition number of the
general-`q` Fabius Toeplitz rows is at least `1000` at that base.
This turns "the limit grows without bound as `q ↑ 1`" from a remark
into an exhibited instance. -/
theorem thousand_le_qConditionNumberLimit :
    (1000 : ℝ) ≤ qConditionNumberLimit (999 / 1000) := by
  have h := one_div_one_sub_le_qConditionNumberLimit
    (q := (999 / 1000 : ℝ)) (by norm_num) (by norm_num)
  have hval : (1 : ℝ) / (1 - 999 / 1000) = 1000 := by norm_num
  linarith [h, hval]

/-! ## The effective Weierstrass bound, and its limits -/

/-- **The effective Weierstrass lower bound**
`1 - q/(1-q) ≤ (q;q)_∞`, for `0 ≤ q < 1`.

Unlike `qPochhammerInf_self_pos` this bound is explicit and
computable, but it is informative only while the deficit budget
`∑_j q^{j+1} = q/(1-q)` stays below one, that is only for `q < 1/2`.
`weierstrass_bound_vacuous_at_three_quarters` records that it is
vacuous already at `q = 3/4`, which is why the positivity above goes
through the logarithm instead. -/
theorem one_sub_geom_le_qPochhammerInf_self {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    1 - q * (1 - q)⁻¹ ≤ qPochhammerInf q q := by
  have hu0 : ∀ j : ℕ, (0 : ℝ) ≤ q * q ^ j :=
    fun j => mul_nonneg hq0 (pow_nonneg hq0 j)
  have hu1 : ∀ j : ℕ, q * q ^ j ≤ 1 := by
    intro j
    have h2 : q * q ^ j ≤ q :=
      mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
    linarith
  have hsum : Summable fun j : ℕ => q * q ^ j :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left q
  have hprod : Multipliable fun j : ℕ => 1 - q * q ^ j :=
    multipliable_one_sub_mul_pow q hq0 hq1
  have hW := one_sub_tsum_le_tprod_one_sub
    (fun j : ℕ => q * q ^ j) hu0 hu1 hsum hprod
  have htsum : (∑' j : ℕ, q * q ^ j) = q * (1 - q)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  show 1 - q * (1 - q)⁻¹ ≤ ∏' j : ℕ, (1 - q * q ^ j)
  calc
    1 - q * (1 - q)⁻¹ = 1 - ∑' j : ℕ, q * q ^ j := by rw [htsum]
    _ ≤ ∏' j : ℕ, (1 - q * q ^ j) := hW

/-- **Guard: the unpeeled Weierstrass bound is vacuous at `q = 3/4`.**
At `q = 3/4` the bound of `one_sub_geom_le_qPochhammerInf_self` reads
`1 - 3 = -2`, which is negative and therefore says nothing about the
positivity of `(3/4; 3/4)_∞`.  That the *unpeeled* bound says nothing
there is thus a theorem, not an assertion; a peeling argument on the
tail would still reach the whole range, which is why the logarithm
route is used instead. -/
theorem weierstrass_bound_vacuous_at_three_quarters :
    1 - (3 / 4 : ℝ) * (1 - 3 / 4)⁻¹ < 0 := by
  norm_num

end Fabius
