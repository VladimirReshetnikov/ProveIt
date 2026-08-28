import FabiusFunction.GeometricResidualMoments
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Unconditionally summable evaluation of finite power-series filters

The algebraic operator in `FinitePowerSeriesFilter` acts diagonally on
formal coefficients.  This module supplies its convergent-series analogue.
For coefficients `a m` in a normed additive group carrying a module structure
and a finite family of scalar nodes and weights, put

`sum i in s, sum' m, weight i • ((node i * z) ^ m • a m)`.

If the displayed weighted series is summable at each of the finitely many
sampled points, then the finite sum may be interchanged with the infinite
series.  The coefficient in degree `m` is multiplied by the same finite node
moment as in the formal theory.  A zero weight makes its weighted series
identically zero, so no convergence of the corresponding unweighted sample
is required.  No completeness assumption is needed: summability is assumed
exactly for the series which are interchanged.

Finite moment exactness at an arbitrary target then splits the analytic
filter into its reproduced finite head and an exact infinite tail.  At
target zero, the head is just `a 0`; this keeps the essential `0 ^ 0 = 1`
boundary separate from all positive degrees.  Finally, exact geometric rows
and geometric Lagrange weights inherit the denominator-free Gaussian
residual multiplier in every term of the tail.

Here bare `Summable` and `∑'` have Mathlib's default *unconditional*
summation semantics.  Thus the results do not cover a series which converges
only in its natural order at a boundary point; such results require the
separate conditional summation filter.  The theorems make no positivity,
order, radius-of-convergence, asymptotic, or uniform-convergence claim.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-! ## Arbitrary finite filters -/

/-- Analytic evaluation of a finite rescaling filter.

The coefficient sequence takes values in an arbitrary normed additive group
with a module structure over a commutative semiring.  The definition itself
is total; the theorems below impose unconditional summability on each
weighted sampled series.  In particular, zero-weight samples impose no
convergence obligation. -/
noncomputable def finiteAnalyticSeriesFilter
    {ι 𝕜 E : Type*} [CommSemiring 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Finset ι) (node weight : ι → 𝕜)
    (a : ℕ → E) (z : 𝕜) : E :=
  ∑ i ∈ s, ∑' m : ℕ, weight i • ((node i * z) ^ m • a m)

private theorem sum_weight_smul_seriesTerm
    {ι 𝕜 E : Type*} [CommSemiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    (s : Finset ι) (node weight : ι → 𝕜)
    (z : 𝕜) (m : ℕ) (v : E) :
    (∑ i ∈ s, weight i • ((node i * z) ^ m • v)) =
      ((∑ i ∈ s, weight i * node i ^ m) * z ^ m) • v := by
  calc
    (∑ i ∈ s, weight i • ((node i * z) ^ m • v)) =
        ∑ i ∈ s, (weight i * (node i * z) ^ m) • v := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [smul_smul]
    _ = (∑ i ∈ s, weight i * (node i * z) ^ m) • v := by
      rw [Finset.sum_smul]
    _ = ((∑ i ∈ s, weight i * node i ^ m) * z ^ m) • v := by
      congr 1
      calc
        (∑ i ∈ s, weight i * (node i * z) ^ m) =
            ∑ i ∈ s, (weight i * node i ^ m) * z ^ m := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [mul_pow, ← mul_assoc]
        _ = (∑ i ∈ s, weight i * node i ^ m) * z ^ m := by
          rw [Finset.sum_mul]

/-- The diagonal series of a finite analytic filter is summable whenever
every weighted sampled series is unconditionally summable.  This hypothesis
is automatic at zero-weight nodes. -/
theorem summable_finiteAnalyticSeriesFilter_diagonal
    {ι 𝕜 E : Type*} [CommSemiring 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Finset ι) (node weight : ι → 𝕜)
    (a : ℕ → E) (z : 𝕜)
    (hsum : ∀ i ∈ s, Summable fun m : ℕ ↦
      weight i • ((node i * z) ^ m • a m)) :
    Summable fun m : ℕ ↦
      ((∑ i ∈ s, weight i * node i ^ m) * z ^ m) • a m := by
  refine (summable_sum hsum).congr ?_
  intro m
  exact sum_weight_smul_seriesTerm s node weight z m (a m)

/-- **Finite analytic filters act diagonally.**

Interchanging the finite node sum with the unconditionally summable weighted
coefficient series multiplies degree `m` by the finite moment
`sum i in s, weight i * node i ^ m`. -/
theorem finiteAnalyticSeriesFilter_eq_tsum
    {ι 𝕜 E : Type*} [CommSemiring 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Finset ι) (node weight : ι → 𝕜)
    (a : ℕ → E) (z : 𝕜)
    (hsum : ∀ i ∈ s, Summable fun m : ℕ ↦
      weight i • ((node i * z) ^ m • a m)) :
    finiteAnalyticSeriesFilter s node weight a z =
      ∑' m : ℕ,
        ((∑ i ∈ s, weight i * node i ^ m) * z ^ m) • a m := by
  rw [finiteAnalyticSeriesFilter]
  calc
    (∑ i ∈ s, ∑' m : ℕ,
        weight i • ((node i * z) ^ m • a m)) =
        ∑' m : ℕ, ∑ i ∈ s,
        weight i • ((node i * z) ^ m • a m) := by
      exact (Summable.tsum_finsetSum hsum).symm
    _ = ∑' m : ℕ,
        ((∑ i ∈ s, weight i * node i ^ m) * z ^ m) • a m := by
      apply tsum_congr
      intro m
      exact sum_weight_smul_seriesTerm s node weight z m (a m)

/-! ## Exact heads and analytic tails -/

/-- **Exact finite head and exact infinite tail.**

If the finite row reproduces evaluation at `target` through degree `p`, its
analytic action is the reproduced Taylor head through degree `p` plus the
uncancelled diagonal tail.  The statement is valid for `p = 0` and for
arbitrary targets and nodes. -/
theorem finiteAnalyticSeriesFilter_eq_head_add_tail_of_exact
    {ι 𝕜 E : Type*} [CommSemiring 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Finset ι) (node weight : ι → 𝕜)
    (target : 𝕜) (p : ℕ) (a : ℕ → E) (z : 𝕜)
    (hmoment : ∀ d ≤ p,
      ∑ i ∈ s, weight i * node i ^ d = target ^ d)
    (hsum : ∀ i ∈ s, Summable fun m : ℕ ↦
      weight i • ((node i * z) ^ m • a m)) :
    finiteAnalyticSeriesFilter s node weight a z =
      (∑ d ∈ Finset.range (p + 1), (target * z) ^ d • a d) +
        ∑' r : ℕ,
          ((∑ i ∈ s,
              weight i * node i ^ (p + 1 + r)) *
            z ^ (p + 1 + r)) • a (p + 1 + r) := by
  have hdiag := summable_finiteAnalyticSeriesFilter_diagonal
    s node weight a z hsum
  calc
    finiteAnalyticSeriesFilter s node weight a z =
        ∑' m : ℕ,
          ((∑ i ∈ s, weight i * node i ^ m) * z ^ m) • a m :=
      finiteAnalyticSeriesFilter_eq_tsum s node weight a z hsum
    _ = (∑ d ∈ Finset.range (p + 1),
          ((∑ i ∈ s, weight i * node i ^ d) * z ^ d) • a d) +
        ∑' r : ℕ,
          ((∑ i ∈ s,
              weight i * node i ^ (r + (p + 1))) *
            z ^ (r + (p + 1))) • a (r + (p + 1)) :=
      (hdiag.sum_add_tsum_nat_add (p + 1)).symm
    _ = (∑ d ∈ Finset.range (p + 1), (target * z) ^ d • a d) +
        ∑' r : ℕ,
          ((∑ i ∈ s,
              weight i * node i ^ (p + 1 + r)) *
            z ^ (p + 1 + r)) • a (p + 1 + r) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro d hd
        rw [hmoment d (Nat.le_of_lt_succ (Finset.mem_range.mp hd)), mul_pow]
      · apply tsum_congr
        intro r
        rw [Nat.add_comm r (p + 1)]

/-- At target zero, exactness preserves the constant term and leaves an
explicit tail beginning in degree `p + 1`.  In particular, degree zero is
never passed through a positive-degree residual formula. -/
theorem finiteAnalyticSeriesFilter_eq_constant_add_tail_of_exact_zero
    {ι 𝕜 E : Type*} [CommSemiring 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Finset ι) (node weight : ι → 𝕜)
    (p : ℕ) (a : ℕ → E) (z : 𝕜)
    (hmoment : ∀ d ≤ p,
      ∑ i ∈ s, weight i * node i ^ d = (0 : 𝕜) ^ d)
    (hsum : ∀ i ∈ s, Summable fun m : ℕ ↦
      weight i • ((node i * z) ^ m • a m)) :
    finiteAnalyticSeriesFilter s node weight a z =
      a 0 + ∑' r : ℕ,
        ((∑ i ∈ s,
            weight i * node i ^ (p + 1 + r)) *
          z ^ (p + 1 + r)) • a (p + 1 + r) := by
  rw [finiteAnalyticSeriesFilter_eq_head_add_tail_of_exact
    s node weight 0 p a z hmoment hsum]
  have hhead :
      (∑ d ∈ Finset.range (p + 1), ((0 : 𝕜) * z) ^ d • a d) =
        a 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro d hd hd0
      rw [zero_mul, zero_pow hd0, zero_smul]
    · intro hzero
      exact (hzero (Finset.mem_range.mpr (Nat.succ_pos p))).elim
  rw [hhead]

/-! ## Geometric filters and Gaussian residuals -/

/-- The analytic series filter on the geometric nodes
`1, q, ..., q ^ p`. -/
noncomputable def geometricAnalyticSeriesFilter
    {𝕜 E : Type*} [CommSemiring 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    (q : 𝕜) (p : ℕ) (weight : ℕ → 𝕜)
    (a : ℕ → E) (z : 𝕜) : E :=
  finiteAnalyticSeriesFilter (Finset.range (p + 1))
    (fun j ↦ q ^ j) weight a z

/-- **Exact analytic Gaussian residual for a geometric row.**

Every row which is exact at zero through degree `p` preserves `a 0` and
multiplies its term in degree `p + 1 + r` by
`(-1)^p q^choose(p+1,2) gaussianBinomial q (p+r) p`.
The scalar ring may have zero divisors.  No division, node distinctness, or
nonzeroness hypothesis is used.  Summability is required only at nodes whose
weight is nonzero. -/
theorem geometricAnalyticSeriesFilter_eq_constant_add_gaussian_tsum
    {𝕜 E : Type*} [CommRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E]
    (q : 𝕜) (p : ℕ) (weight : ℕ → 𝕜)
    (a : ℕ → E) (z : 𝕜)
    (hmoment : ∀ d ≤ p,
      ∑ j ∈ Finset.range (p + 1),
        weight j * (q ^ j) ^ d = (0 : 𝕜) ^ d)
    (hsum : ∀ j ∈ Finset.range (p + 1), weight j ≠ 0 →
      Summable fun m : ℕ ↦ (q ^ j * z) ^ m • a m) :
    geometricAnalyticSeriesFilter q p weight a z =
      a 0 + ∑' r : ℕ,
        (((-1 : 𝕜) ^ p * q ^ ((p + 1).choose 2) *
            gaussianBinomial q (p + r) p) *
          z ^ (p + 1 + r)) • a (p + 1 + r) := by
  have hweighted : ∀ j ∈ Finset.range (p + 1), Summable fun m : ℕ ↦
      weight j • ((q ^ j * z) ^ m • a m) := by
    intro j hj
    by_cases hw : weight j = 0
    · simp [hw]
    · exact (hsum j hj hw).const_smul (weight j)
  rw [geometricAnalyticSeriesFilter,
    finiteAnalyticSeriesFilter_eq_constant_add_tail_of_exact_zero
      (Finset.range (p + 1)) (fun j ↦ q ^ j) weight p a z hmoment hweighted]
  congr 1
  apply tsum_congr
  intro r
  rw [sum_weight_mul_geometric_pow_succ_add q p weight hmoment r]

/-- The analytic geometric Lagrange filter has the Gaussian residual tail at
every scale `z`.  Distinctness is used only to supply its finite exactness,
and zero Lagrange weights impose no convergence condition. -/
theorem geometricLagrangeAnalyticSeriesFilter_eq_constant_add_gaussian_tsum
    {𝕜 E : Type*} [Field 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E]
    (q : 𝕜) (p : ℕ) (a : ℕ → E) (z : 𝕜)
    (hnode : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)))
    (hsum : ∀ j ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p j ≠ 0 →
        Summable fun m : ℕ ↦ (q ^ j * z) ^ m • a m) :
    geometricAnalyticSeriesFilter q p (geometricLagrangeWeight q p) a z =
      a 0 + ∑' r : ℕ,
        (((-1 : 𝕜) ^ p * q ^ ((p + 1).choose 2) *
            gaussianBinomial q (p + r) p) *
          z ^ (p + 1 + r)) • a (p + 1 + r) := by
  exact geometricAnalyticSeriesFilter_eq_constant_add_gaussian_tsum
    q p (geometricLagrangeWeight q p) a z
    (fun d hd ↦ sum_geometricLagrangeWeight_mul_pow q p d hnode hd) hsum

/-- Shifted-scale form of the analytic geometric Lagrange residual.  Setting
`z = q ^ start` combines the sample scale with the triangular residual
factor into the exponent `start * (p + 1 + r) + choose(p+1,2)`. -/
theorem geometricLagrangeAnalyticSeriesFilter_shifted
    {𝕜 E : Type*} [Field 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E]
    [ContinuousConstSMul 𝕜 E]
    (q : 𝕜) (p start : ℕ) (a : ℕ → E)
    (hnode : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)))
    (hsum : ∀ j ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p j ≠ 0 →
        Summable fun m : ℕ ↦ (q ^ j * q ^ start) ^ m • a m) :
    geometricAnalyticSeriesFilter q p (geometricLagrangeWeight q p) a
        (q ^ start) =
      a 0 + ∑' r : ℕ,
        ((-1 : 𝕜) ^ p *
          q ^ (start * (p + 1 + r) + (p + 1).choose 2) *
            gaussianBinomial q (p + r) p) • a (p + 1 + r) := by
  rw [geometricLagrangeAnalyticSeriesFilter_eq_constant_add_gaussian_tsum
    q p a (q ^ start) hnode hsum]
  congr 1
  apply tsum_congr
  intro r
  congr 1
  rw [← pow_mul, pow_add]
  ring

end

end Fabius
