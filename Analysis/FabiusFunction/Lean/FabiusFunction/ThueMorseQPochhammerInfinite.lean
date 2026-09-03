import FabiusFunction.QPochhammerInfinite
import FabiusFunction.ThueMorseBasicLemmas
import FabiusFunction.ThueMorseQPochhammer
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The infinite bigraded Thue–Morse form of the q-Pochhammer symbol

`ThueMorseQPochhammer` proves the *finite* bigraded bridge

`∑_{n<2^N} ε(n)·z^{w(n)}·q^{σ(n)} = (z;q)_N`

over an arbitrary commutative ring, with no hypothesis on `z` or `q`
(`sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`).  This module
passes to the limit over `ℂ`: for every nome `q` in the open unit disc and
**every** `z : ℂ` whatsoever,

`∑'_n ε(n)·z^{w(n)}·q^{σ(n)} = (z;q)_∞`,

where `w = binaryWeight` is the binary digit sum, `σ = bitPositionSum` the sum
of the positions of the one bits, and `ε(n) = (-1)^{w(n)}` the Thue–Morse
sign.  So the whole Thue–Morse sequence, not a dyadic truncation of it,
enumerates the infinite q-Pochhammer symbol, bigraded by the two digit
statistics.

## Why the series converges, for every `z`

The dyadic partial sums of the *moduli* are exactly a finite product.  The
bit-position generating identity `prod_one_add_mul_pow_bitPositionSum` holds
over any commutative semiring, so at `R = ℝ` with `y = ‖z‖` and nome `‖q‖`,

`∑_{n<2^N} ‖z‖^{w(n)}·‖q‖^{σ(n)} = ∏_{j<N} (1 + ‖z‖·‖q‖^j)`
`  ≤ exp(‖z‖·(1-‖q‖)⁻¹),`

the last step by `1 + t ≤ exp t` and the geometric bound
`∑_{j<N} ‖z‖·‖q‖^j ≤ ‖z‖·(1-‖q‖)⁻¹`.  The terms being nonnegative and
`m ≤ 2^m`, *every* partial sum `∑_{n<m}` is bounded by that same constant, so
`summable_of_sum_range_le` gives absolute summability with no restriction on
`z` at all: `z` enters the bound only through the finite constant
`exp(‖z‖·(1-‖q‖)⁻¹)`, because in each factor `1 + ‖z‖·‖q‖^j` it is paired
with a geometrically small power of the nome.

The limit step is then uniqueness of limits: the partial sums along the
subsequence `N ↦ 2^N` converge to the `tsum` (a subsequence of a convergent
sequence), and by the finite bridge they are the finite symbols `(z;q)_N`,
which converge to `(z;q)_∞` by
`tendsto_finiteQPochhammerIn_qPochhammerInfIn`.

## Relation to the rest of the atlas

The Thue–Morse and q-Pochhammer layers were already connected in two places;
this module is the missing third, and is positioned between them.

* `sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`
  (`ThueMorseQPochhammer`) — the finite, purely algebraic, hypothesis-free
  bridge whose limit is taken here.
* `qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign`
  (`ThueMorseEulerFunction`) — the infinite but *multiplicative* sibling
  `(q;q)_∞ = ∏'_k E(q^{2k+1})`, which factors Euler's function through the
  Thue–Morse *generating function*.  The identity below instead writes an
  arbitrary `(z;q)_∞` as a single Thue–Morse *sign sum*, bigraded by `w`
  and `σ`.

Everything is stated over `ℂ` only.  The finite bridge is type-generic, but
the convergence layer for `qPochhammerInfIn` lives in normed rings and the
summability argument above is a normed-space argument; stating the identity
at a general complete normed field is a separate job.

## Main declarations

* `sum_range_pow_binaryWeight_mul_pow_bitPositionSum_le` — the uniform real
  bound `∑_{i<m} x^{w(i)}·r^{σ(i)} ≤ exp(x·(1-r)⁻¹)` for `0 ≤ x`, `0 ≤ r < 1`.
* `summable_pow_binaryWeight_mul_pow_bitPositionSum` — its consequence, the
  summability of the nonnegative bigraded family.
* `summable_thueMorseSign_mul_pow_bigraded` — absolute summability over `ℂ`.
* `hasSum_thueMorseSign_mul_pow_bigraded` and
  `tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn` — **the
  identity**.
* `tsum_thueMorseSign_mul_pow_bitPositionSum_eq_zero` — its `z = 1` face,
  `∑'_n ε(n)·q^{σ(n)} = 0`, the infinite counterpart of the dyadic Prouhet
  cancellation `sum_thueMorseSign_mul_pow_bitPositionSum_eq_zero`.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-! ## A uniform bound for the nonnegative bigraded partial sums -/

/-- **The bigraded partial sums of a nonnegative bigraded family are
uniformly bounded.**  For `0 ≤ x` and `0 ≤ r < 1`, every partial sum

`∑_{i<m} x^{w(i)}·r^{σ(i)} ≤ exp(x·(1-r)⁻¹)`,

with a bound independent of `m` and of any smallness assumption on `x`.

The mechanism is the bit-position generating identity
`prod_one_add_mul_pow_bitPositionSum`, which is a commutative-semiring
statement and therefore applies at `R = ℝ`: it turns the *dyadic* block sum
`∑_{i<2^m}` into the finite product `∏_{j<m} (1 + x·r^j)`, which `1 + t ≤ exp t`
and the geometric bound `∑_{j<m} x·r^j ≤ x·(1-r)⁻¹` control.  A general range
`range m` is caught inside the dyadic block `range (2^m)` because `m ≤ 2^m`
and the terms are nonnegative. -/
theorem sum_range_pow_binaryWeight_mul_pow_bitPositionSum_le
    {x r : ℝ} (hx : 0 ≤ x) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, x ^ binaryWeight i * r ^ bitPositionSum i ≤
      Real.exp (x * (1 - r)⁻¹) := by
  have hnn : ∀ i : ℕ, (0 : ℝ) ≤ x ^ binaryWeight i * r ^ bitPositionSum i :=
    fun i => mul_nonneg (pow_nonneg hx _) (pow_nonneg hr0 _)
  have hterm : ∀ j : ℕ, (0 : ℝ) ≤ x * r ^ j := fun j => mul_nonneg hx (pow_nonneg hr0 j)
  have hgeom : Summable fun j : ℕ => x * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left x
  have hgeomSum : ∑ j ∈ Finset.range m, x * r ^ j ≤ x * (1 - r)⁻¹ := by
    have h := hgeom.sum_le_tsum (Finset.range m) fun j _ => hterm j
    rwa [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at h
  have hexp : ∏ j ∈ Finset.range m, (1 + x * r ^ j) ≤
      Real.exp (∑ j ∈ Finset.range m, x * r ^ j) :=
    Real.prod_one_add_le_exp_sum (Finset.range m) hterm
  calc ∑ i ∈ Finset.range m, x ^ binaryWeight i * r ^ bitPositionSum i
      ≤ ∑ i ∈ Finset.range (2 ^ m), x ^ binaryWeight i * r ^ bitPositionSum i :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr Nat.lt_two_pow_self.le) fun i _ _ => hnn i
    _ = ∏ j ∈ Finset.range m, (1 + x * r ^ j) :=
        (prod_one_add_mul_pow_bitPositionSum x r m).symm
    _ ≤ Real.exp (∑ j ∈ Finset.range m, x * r ^ j) := hexp
    _ ≤ Real.exp (x * (1 - r)⁻¹) := Real.exp_le_exp.mpr hgeomSum

/-- **Summability of the nonnegative bigraded family.**  For `0 ≤ x` and
`0 ≤ r < 1` the family `n ↦ x^{w(n)}·r^{σ(n)}` is summable, with no upper
bound imposed on `x`: the uniform bound of
`sum_range_pow_binaryWeight_mul_pow_bitPositionSum_le` feeds
`summable_of_sum_range_le`. -/
theorem summable_pow_binaryWeight_mul_pow_bitPositionSum
    {x r : ℝ} (hx : 0 ≤ x) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => x ^ binaryWeight n * r ^ bitPositionSum n :=
  summable_of_sum_range_le (c := Real.exp (x * (1 - r)⁻¹))
    (fun n => mul_nonneg (pow_nonneg hx _) (pow_nonneg hr0 _))
    fun m => sum_range_pow_binaryWeight_mul_pow_bitPositionSum_le hx hr0 hr1 m

/-! ## Absolute summability over `ℂ` -/

/-- **The bigraded Thue–Morse family is absolutely summable** for every
`z : ℂ` and every nome `q` with `‖q‖ < 1`.  The Thue–Morse sign has modulus
one (`norm_thueMorseSign_complex`), so the moduli of the terms are exactly
`‖z‖^{w(n)}·‖q‖^{σ(n)}`, which
`summable_pow_binaryWeight_mul_pow_bitPositionSum` sums. -/
theorem summable_thueMorseSign_mul_pow_bigraded (z : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ =>
      (thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n := by
  have hreal : Summable fun n : ℕ => ‖z‖ ^ binaryWeight n * ‖q‖ ^ bitPositionSum n :=
    summable_pow_binaryWeight_mul_pow_bitPositionSum (norm_nonneg z) (norm_nonneg q) hq
  refine Summable.of_norm (hreal.congr fun n => ?_)
  show ‖z‖ ^ binaryWeight n * ‖q‖ ^ bitPositionSum n =
    ‖(thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n‖
  rw [norm_mul, norm_mul, norm_thueMorseSign_complex, one_mul, norm_pow, norm_pow]

/-! ## The infinite bigraded identity -/

/-- **The infinite q-Pochhammer symbol is a Thue–Morse bigraded sum.**  For
every `z : ℂ` and every nome `q` with `‖q‖ < 1`,

`∑'_n ε(n)·z^{w(n)}·q^{σ(n)} = (z;q)_∞`.

This is the infinite counterpart of the finite bridge
`sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`, and its proof is
that bridge plus uniqueness of limits: the partial sums along the dyadic
subsequence `N ↦ 2^N` converge to the `tsum` because the family is summable
and `N ↦ 2^N` tends to infinity, while by the bridge they *are* the finite
symbols `(z;q)_N`, which converge to `(z;q)_∞`. -/
theorem tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn
    (z : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' n : ℕ, (thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n =
      qPochhammerInfIn z q := by
  have hpartial :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
          (thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n) atTop
        (𝓝 (∑' n : ℕ,
          (thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n)) :=
    (summable_thueMorseSign_mul_pow_bigraded z hq).hasSum.tendsto_sum_nat
  have hpow : Tendsto (fun N : ℕ => 2 ^ N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun N hN => hN.trans Nat.lt_two_pow_self.le⟩
  have hblock :
      Tendsto (fun N : ℕ => finiteQPochhammerIn z q N) atTop
        (𝓝 (∑' n : ℕ,
          (thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n)) := by
    refine Filter.Tendsto.congr ?_ (hpartial.comp hpow)
    intro N
    exact sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn z q N
  exact tendsto_nhds_unique hblock (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq)

/-- The identity in `HasSum` form: the bigraded Thue–Morse family has
unordered sum `(z;q)_∞`. -/
theorem hasSum_thueMorseSign_mul_pow_bigraded (z : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
        (thueMorseSign n : ℂ) * z ^ binaryWeight n * q ^ bitPositionSum n)
      (qPochhammerInfIn z q) := by
  rw [← tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn z hq]
  exact (summable_thueMorseSign_mul_pow_bigraded z hq).hasSum

/-- **Infinite bit-position Prouhet cancellation.**  For every complex nome
with `‖q‖ < 1`,

`∑'_n ε(n)·q^{σ(n)} = 0`.

This is the `z = 1` face of
`tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn`: the `j = 0` factor
of `(1;q)_∞` is `1 - 1·q^0 = 0`.  Unlike the finite version
`sum_thueMorseSign_mul_pow_bitPositionSum_eq_zero`, which needs the summation
range to be a full dyadic block `range (2^N)` with `N ≥ 1`, the cancellation
here is of the whole absolutely convergent series, so no block structure is
imposed on the index set. -/
theorem tsum_thueMorseSign_mul_pow_bitPositionSum_eq_zero {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' n : ℕ, (thueMorseSign n : ℂ) * q ^ bitPositionSum n = 0 := by
  have hcongr : ∑' n : ℕ, (thueMorseSign n : ℂ) * q ^ bitPositionSum n =
      ∑' n : ℕ, (thueMorseSign n : ℂ) * (1 : ℂ) ^ binaryWeight n * q ^ bitPositionSum n :=
    tsum_congr fun n => by rw [one_pow, mul_one]
  rw [hcongr, tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn (1 : ℂ) hq]
  exact tprod_of_exists_eq_zero
    ⟨0, show (1 : ℂ) - 1 * q ^ (0 : ℕ) = 0 by simp⟩

end Fabius
