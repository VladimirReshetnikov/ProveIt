import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Lagrange

/-!
# Geometric Lagrange weights and finite Richardson exactness

This module packages the algebra behind finite Richardson extrapolation on a
geometric grid.  It deliberately builds on Mathlib's `Lagrange` namespace:
the weights are evaluations of Mathlib's Lagrange basis polynomials, and the
exactness theorem is obtained from `Lagrange.eq_interpolate` rather than from
a second interpolation construction.

The first layer works for an arbitrary finite family of distinct field-valued
nodes.  Its evaluation weights reproduce every polynomial of degree strictly
below the number of nodes.  At the first omitted degree, the defect is exactly
the nodal polynomial.  The second layer specializes the nodes to
`q ^ k`, `0 <= k <= n`, and the evaluation point to zero.  Thus the moments
through degree `n` are `0 ^ d`; in particular degree zero is normalized to
one, with Lean's convention `0 ^ 0 = 1`, while positive degrees vanish.  The
first surviving moment is also evaluated explicitly.

Finally, the same scalar identities are lifted to an arbitrary module.  If a
block of samples beginning at `start` is a constant plus the first `n`
geometric error modes, its weighted sum is exactly the constant.  No positive
degree or positive starting-index assumption is used, so `n = 0` and
`start = 0` are genuine instances of the main theorem.

## Main results

* `sum_lagrangeEvalWeight_mul_eval` reproduces a degree-bounded polynomial at
  an arbitrary evaluation point.
* `sum_lagrangeEvalWeight_mul_pow_card` gives the exact first omitted moment.
* `sum_geometricLagrangeWeight_mul_pow` gives all geometric moments through
  degree `n`, including the `0 ^ 0` boundary.
* `sum_geometricLagrangeWeight_mul_pow_succ` evaluates the first surviving
  moment.
* `geometricLagrange_richardson_exact` is module-valued finite Richardson
  exactness at an arbitrary starting index.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

/-- The Lagrange weight for evaluation at `x`: the value at `x` of the basis
polynomial belonging to node `v i` in the finite indexed family `s`.

The definition itself makes sense without distinct nodes.  Exactness theorems
below take the necessary explicit hypothesis `Set.InjOn v s`. -/
noncomputable def lagrangeEvalWeight
    {F : Type*} [Field F] {ι : Type*}
    (s : Finset ι) (v : ι → F) (x : F) (i : ι) : F := by
  classical
  exact (Lagrange.basis s v i).eval x

/-- Evaluation by finite Lagrange weights.  For distinct nodes, the weighted
sum of the nodal values of a polynomial of degree strictly below `s.card`
equals its value at the target point `x`. -/
theorem sum_lagrangeEvalWeight_mul_eval
    {F : Type*} [Field F] {ι : Type*}
    (s : Finset ι) (v : ι → F) (x : F)
    (hvs : Set.InjOn v s) (p : F[X])
    (hp : p.degree < (s.card : WithBot ℕ)) :
    (∑ i ∈ s, lagrangeEvalWeight s v x i * p.eval (v i)) = p.eval x := by
  classical
  calc
    (∑ i ∈ s, lagrangeEvalWeight s v x i * p.eval (v i)) =
        (Lagrange.interpolate s v (fun i => p.eval (v i))).eval x := by
      rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Polynomial.eval_mul, Polynomial.eval_C, lagrangeEvalWeight]
      exact mul_comm _ _
    _ = p.eval x := by
      rw [← Lagrange.eq_interpolate hvs hp]

/-- Monomial form of finite Lagrange exactness.  Every moment of degree
`d < s.card` reproduces `x ^ d`. -/
theorem sum_lagrangeEvalWeight_mul_pow
    {F : Type*} [Field F] {ι : Type*}
    (s : Finset ι) (v : ι → F) (x : F)
    (hvs : Set.InjOn v s) (d : ℕ) (hd : d < s.card) :
    (∑ i ∈ s, lagrangeEvalWeight s v x i * v i ^ d) = x ^ d := by
  have hdegree :
      (Polynomial.X ^ d : F[X]).degree < (s.card : WithBot ℕ) := by
    simpa using hd
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    sum_lagrangeEvalWeight_mul_eval s v x hvs
      (Polynomial.X ^ d : F[X]) hdegree

/-- Exact first-omitted-degree identity for finite Lagrange evaluation.  At
degree `s.card`, the interpolated monomial differs from `x ^ s.card` by the
nodal polynomial `prod i in s, (x - v i)`.  This statement also covers the
empty family: both sides then vanish. -/
theorem sum_lagrangeEvalWeight_mul_pow_card
    {F : Type*} [Field F] {ι : Type*}
    (s : Finset ι) (v : ι → F) (x : F)
    (hvs : Set.InjOn v s) :
    (∑ i ∈ s, lagrangeEvalWeight s v x i * v i ^ s.card) =
      x ^ s.card - ∏ i ∈ s, (x - v i) := by
  classical
  have hdegrees :
      (Polynomial.X ^ s.card : F[X]).degree =
        (Lagrange.nodal s v).degree := by
    rw [Polynomial.degree_X_pow, Lagrange.degree_nodal]
  have hne : (Polynomial.X ^ s.card : F[X]) ≠ 0 :=
    (Polynomial.monic_X_pow s.card).ne_zero
  have hlead :
      (Polynomial.X ^ s.card : F[X]).leadingCoeff =
        (Lagrange.nodal s v).leadingCoeff :=
    (Polynomial.monic_X_pow s.card).leadingCoeff.trans
      Lagrange.nodal_monic.leadingCoeff.symm
  have hdegree :
      (Polynomial.X ^ s.card - Lagrange.nodal s v).degree <
        (s.card : WithBot ℕ) := by
    simpa using Polynomial.degree_sub_lt hdegrees hne hlead
  calc
    (∑ i ∈ s, lagrangeEvalWeight s v x i * v i ^ s.card) =
        ∑ i ∈ s, lagrangeEvalWeight s v x i *
          (Polynomial.X ^ s.card - Lagrange.nodal s v).eval (v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Lagrange.eval_nodal_at_node hi, sub_zero]
    _ = (Polynomial.X ^ s.card - Lagrange.nodal s v).eval x :=
      sum_lagrangeEvalWeight_mul_eval s v x hvs
        (Polynomial.X ^ s.card - Lagrange.nodal s v) hdegree
    _ = x ^ s.card - ∏ i ∈ s, (x - v i) := by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Lagrange.eval_nodal]

/-- Module-valued finite Lagrange exactness.  A truncated power sum with
coefficients in any `F`-module may be interpolated coefficientwise: weighting
its values at `v i` evaluates the same power sum at `x`.

Only an additive commutative monoid structure is needed on the target; no
subtraction, topology, or norm is involved. -/
theorem sum_lagrangeEvalWeight_smul_sum_pow
    {F M : Type*} [Field F] [AddCommMonoid M] [Module F M]
    {ι : Type*} (s : Finset ι) (v : ι → F) (x : F)
    (hvs : Set.InjOn v s) (coeff : ℕ → M) :
    (∑ i ∈ s, lagrangeEvalWeight s v x i •
        (∑ d ∈ Finset.range s.card, v i ^ d • coeff d)) =
      ∑ d ∈ Finset.range s.card, x ^ d • coeff d := by
  classical
  calc
    (∑ i ∈ s, lagrangeEvalWeight s v x i •
        (∑ d ∈ Finset.range s.card, v i ^ d • coeff d)) =
        ∑ i ∈ s, ∑ d ∈ Finset.range s.card,
          (lagrangeEvalWeight s v x i * v i ^ d) • coeff d := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [smul_smul]
    _ = ∑ d ∈ Finset.range s.card, ∑ i ∈ s,
        (lagrangeEvalWeight s v x i * v i ^ d) • coeff d := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.range s.card, x ^ d • coeff d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_smul,
        sum_lagrangeEvalWeight_mul_pow s v x hvs d
          (Finset.mem_range.mp hd)]

/-- Evaluation-at-zero Lagrange weight for the geometric nodes
`1, q, ..., q ^ n`.  The distinctness of these nodes is deliberately not
baked into the definition; public identities accept it as an explicit
`Set.InjOn` hypothesis. -/
noncomputable def geometricLagrangeWeight
    {F : Type*} [Field F] (q : F) (n k : ℕ) : F :=
  lagrangeEvalWeight (Finset.range (n + 1)) (fun j : ℕ => q ^ j) 0 k

/-- All geometric Lagrange moments through degree `n`.  The right side is
left as `0 ^ d` so that degree zero records the normalization as the genuine
boundary value `0 ^ 0 = 1`, rather than through a separate convention. -/
theorem sum_geometricLagrangeWeight_mul_pow
    {F : Type*} [Field F] (q : F) (n d : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)))
    (hd : d ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k * (q ^ k) ^ d) = (0 : F) ^ d := by
  have hd' : d < (Finset.range (n + 1)).card := by
    simpa only [Finset.card_range] using Nat.lt_succ_iff.mpr hd
  simpa only [geometricLagrangeWeight] using
    sum_lagrangeEvalWeight_mul_pow
      (Finset.range (n + 1)) (fun k : ℕ => q ^ k) 0 hnode d hd'

/-- The geometric evaluation weights have total mass one, including the
singleton grid at `n = 0`.  This is the degree-zero case of
`sum_geometricLagrangeWeight_mul_pow`. -/
theorem sum_geometricLagrangeWeight
    {F : Type*} [Field F] (q : F) (n : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1))) :
    (∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k) = 1 := by
  simpa only [pow_zero, mul_one] using
    sum_geometricLagrangeWeight_mul_pow q n 0 hnode (Nat.zero_le n)

/-- Every positive geometric moment through degree `n` vanishes.  Degree
zero is intentionally excluded here and retained by
`sum_geometricLagrangeWeight`, so the two boundary behaviours cannot be
silently conflated. -/
theorem sum_geometricLagrangeWeight_mul_pow_eq_zero
    {F : Type*} [Field F] (q : F) (n d : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)))
    (hdpos : 0 < d) (hd : d ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k * (q ^ k) ^ d) = 0 := by
  simpa only [zero_pow hdpos.ne'] using
    sum_geometricLagrangeWeight_mul_pow q n d hnode hd

/-- Product form of the first surviving geometric moment.  It is the exact
degree-`n + 1` interpolation defect at zero and remains valid for `n = 0`. -/
theorem sum_geometricLagrangeWeight_mul_pow_succ_product
    {F : Type*} [Field F] (q : F) (n : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1))) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k * (q ^ k) ^ (n + 1)) =
      -∏ k ∈ Finset.range (n + 1), -(q ^ k) := by
  simpa only [geometricLagrangeWeight, Finset.card_range,
    zero_pow (Nat.succ_ne_zero n), zero_sub] using
    sum_lagrangeEvalWeight_mul_pow_card
      (Finset.range (n + 1)) (fun k : ℕ => q ^ k) 0 hnode

/-- Closed form of the first surviving geometric moment:
`(-1)^n q^(n(n+1)/2)`.  The triangular exponent is written using natural
division, which is exact for the product of the powers `q ^ k` over
`0 <= k <= n`. -/
theorem sum_geometricLagrangeWeight_mul_pow_succ
    {F : Type*} [Field F] (q : F) (n : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1))) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k * (q ^ k) ^ (n + 1)) =
      (-1 : F) ^ n * q ^ (n * (n + 1) / 2) := by
  rw [sum_geometricLagrangeWeight_mul_pow_succ_product q n hnode,
    Finset.prod_neg, Finset.card_range, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id]
  simp [pow_succ, Nat.mul_comm]

/-- Module-valued finite Richardson exactness on a geometric grid.  If the
sample at `start + k` is a constant `limit` plus the first `n` modes
`(q ^ (start + k)) ^ (d + 1)`, then the evaluation-at-zero weights recover
`limit` exactly.

The theorem has no positivity or nonzero assumptions and no side condition on
`start`.  For `n = 0` the error sum is empty and the singleton Lagrange weight
is normalized by the same proof. -/
theorem geometricLagrange_richardson_exact
    {F M : Type*} [Field F] [AddCommMonoid M] [Module F M]
    (q : F) (n start : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)))
    (limit : M) (coeff : ℕ → M) :
    (∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k •
      (limit + ∑ d ∈ Finset.range n,
        (q ^ (start + k)) ^ (d + 1) • coeff d)) = limit := by
  classical
  have hmode (d : ℕ) (hd : d < n) :
      (∑ k ∈ Finset.range (n + 1),
        geometricLagrangeWeight q n k *
          (q ^ (start + k)) ^ (d + 1)) = 0 := by
    calc
      (∑ k ∈ Finset.range (n + 1),
          geometricLagrangeWeight q n k *
            (q ^ (start + k)) ^ (d + 1)) =
          (q ^ start) ^ (d + 1) *
            ∑ k ∈ Finset.range (n + 1),
              geometricLagrangeWeight q n k * (q ^ k) ^ (d + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [show q ^ (start + k) = q ^ start * q ^ k by rw [pow_add],
          mul_pow]
        ac_rfl
      _ = 0 := by
        rw [sum_geometricLagrangeWeight_mul_pow_eq_zero q n (d + 1)
          hnode (Nat.succ_pos d) (Nat.succ_le_iff.mpr hd), mul_zero]
  have herror :
      (∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k •
        (∑ d ∈ Finset.range n,
          (q ^ (start + k)) ^ (d + 1) • coeff d)) = 0 := by
    calc
      (∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k •
          (∑ d ∈ Finset.range n,
            (q ^ (start + k)) ^ (d + 1) • coeff d)) =
          ∑ d ∈ Finset.range n, ∑ k ∈ Finset.range (n + 1),
            geometricLagrangeWeight q n k •
              ((q ^ (start + k)) ^ (d + 1) • coeff d) := by
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
      _ = ∑ d ∈ Finset.range n,
          (∑ k ∈ Finset.range (n + 1),
            geometricLagrangeWeight q n k *
              (q ^ (start + k)) ^ (d + 1)) • coeff d := by
        apply Finset.sum_congr rfl
        intro d _hd
        simp_rw [smul_smul]
        rw [← Finset.sum_smul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        rw [hmode d (Finset.mem_range.mp hd), zero_smul]
  calc
    (∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k •
        (limit + ∑ d ∈ Finset.range n,
          (q ^ (start + k)) ^ (d + 1) • coeff d)) =
        (∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k) • limit +
          ∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k •
            (∑ d ∈ Finset.range n,
              (q ^ (start + k)) ^ (d + 1) • coeff d) := by
      simp_rw [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    _ = limit := by
      rw [sum_geometricLagrangeWeight q n hnode, one_smul, herror, add_zero]

/-- Sequence form of `geometricLagrange_richardson_exact`.  It is enough for
the supplied samples `u (start + k)` to have the geometric-mode expansion on
the finite interpolation block; no global formula for `u` is required. -/
theorem geometricLagrange_richardson_exact_of_eq
    {F M : Type*} [Field F] [AddCommMonoid M] [Module F M]
    (q : F) (n start : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)))
    (u : ℕ → M) (limit : M) (coeff : ℕ → M)
    (hu : ∀ k ∈ Finset.range (n + 1),
      u (start + k) = limit + ∑ d ∈ Finset.range n,
        (q ^ (start + k)) ^ (d + 1) • coeff d) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k • u (start + k)) = limit := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        geometricLagrangeWeight q n k • u (start + k)) =
        ∑ k ∈ Finset.range (n + 1), geometricLagrangeWeight q n k •
          (limit + ∑ d ∈ Finset.range n,
            (q ^ (start + k)) ^ (d + 1) • coeff d) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hu k hk]
    _ = limit := geometricLagrange_richardson_exact
      q n start hnode limit coeff

end Fabius
