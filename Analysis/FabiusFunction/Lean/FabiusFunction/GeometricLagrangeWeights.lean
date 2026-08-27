import FabiusFunction.GeometricRichardson
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum

/-!
# Lagrange weights on geometric nodes

This module isolates the interpolation principle behind finite Richardson
filters.  For arbitrary distinct nodes `v i` in a field, the scalar

`lagrangeEvaluationWeight s v x i = (Lagrange.basis s v i).eval x`

is the cardinal weight which reconstructs the value at `x` from the values at
the nodes.  Consequently every polynomial of degree smaller than the number
of nodes satisfies

`sum_i weight_i * P(v i) = P(x)`.

The specialization `x = 0` gives the product appearing in the frontier
report.  On the geometric nodes `1, q, ..., q^(s-1)` it yields weights
`geometricLagrangeWeight q s j` with mass one and moments

`sum_j weight_j * q^(k*j) = 0^k` for `k < s`.

Their generating polynomial is not merely analogous to a Richardson filter:
under the natural distinct-node hypothesis it is exactly
`forwardGeometricRichardsonPolynomial q (s - 1)`.  This identifies Lagrange
interpolation and root-normalized geometric filtering as two descriptions of
the same finite object.  The already established root product then gives the
first uncancelled moment

`sum_j weight_j * q^(s*j) = (-1)^(s-1) q^choose(s, 2)`.

All structural results are field-generic.  The final corollaries discharge the
node hypotheses at `q = 1/4`, the scale used by the Fabius--Rvachev
Richardson expansion.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

section ArbitraryNodes

variable {K ι : Type*} [Field K] [DecidableEq ι]

/-- The Lagrange cardinal weight for reconstructing the value at `x` from
the nodes `v i`, indexed by `s`.

The definition is total, as is Mathlib's Lagrange basis: if nodes collide,
the corresponding inverse differences are zero.  Reconstruction theorems ask
for injectivity exactly where it is mathematically needed. -/
noncomputable def lagrangeEvaluationWeight
    (s : Finset ι) (v : ι → K) (x : K) (i : ι) : K :=
  (Lagrange.basis s v i).eval x

/-- Product formula for an arbitrary Lagrange evaluation weight. -/
theorem lagrangeEvaluationWeight_eq_product
    (s : Finset ι) (v : ι → K) (x : K) (i : ι) :
    lagrangeEvaluationWeight s v x i =
      ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
  rw [lagrangeEvaluationWeight, Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  simp [Lagrange.basisDivisor, div_eq_mul_inv, mul_comm]

/-- Lagrange weights reconstruct every polynomial whose degree is smaller
than the number of interpolation nodes. -/
theorem sum_lagrangeEvaluationWeight_mul_eval_eq
    (s : Finset ι) (v : ι → K) (x : K)
    (hvs : Set.InjOn v s) (P : Polynomial K)
    (hdegree : P.degree < s.card) :
    ∑ i ∈ s, lagrangeEvaluationWeight s v x i * P.eval (v i) =
      P.eval x := by
  calc
    (∑ i ∈ s, lagrangeEvaluationWeight s v x i * P.eval (v i)) =
        (Lagrange.interpolate s v (fun i ↦ P.eval (v i))).eval x := by
          rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
          apply Finset.sum_congr rfl
          intro i _hi
          simp [lagrangeEvaluationWeight, mul_comm]
    _ = P.eval x := by
      rw [← Lagrange.eq_interpolate hvs hdegree]

/-- Monomial form of Lagrange reconstruction.  This is the universal finite
moment identity from which mass and cancellation follow. -/
theorem sum_lagrangeEvaluationWeight_mul_pow_eq
    (s : Finset ι) (v : ι → K) (x : K)
    (hvs : Set.InjOn v s) {k : ℕ} (hk : k < s.card) :
    ∑ i ∈ s, lagrangeEvaluationWeight s v x i * (v i) ^ k = x ^ k := by
  have hdegree : ((Polynomial.X : Polynomial K) ^ k).degree < s.card := by
    rw [Polynomial.degree_X_pow, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact hk
  simpa using sum_lagrangeEvaluationWeight_mul_eval_eq
    s v x hvs ((Polynomial.X : Polynomial K) ^ k) hdegree

/-- The Lagrange cardinal weight for evaluation at zero. -/
noncomputable def lagrangeZeroWeight
    (s : Finset ι) (v : ι → K) (i : ι) : K :=
  lagrangeEvaluationWeight s v 0 i

/-- Product formula for evaluation at zero:
`lambda_i = product_(j != i) (-v_j)/(v_i-v_j)`. -/
theorem lagrangeZeroWeight_eq_product
    (s : Finset ι) (v : ι → K) (i : ι) :
    lagrangeZeroWeight s v i =
      ∏ j ∈ s.erase i, (-v j) / (v i - v j) := by
  simpa [lagrangeZeroWeight] using
    lagrangeEvaluationWeight_eq_product s v (0 : K) i

/-- Evaluation-at-zero weights extract the constant term of every polynomial
of degree smaller than the number of nodes. -/
theorem sum_lagrangeZeroWeight_mul_eval_eq_coeff_zero
    (s : Finset ι) (v : ι → K) (hvs : Set.InjOn v s)
    (P : Polynomial K) (hdegree : P.degree < s.card) :
    ∑ i ∈ s, lagrangeZeroWeight s v i * P.eval (v i) = P.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact sum_lagrangeEvaluationWeight_mul_eval_eq s v 0 hvs P hdegree

/-- Evaluation-at-zero weights have moments `0^k` below the interpolation
degree.  Keeping the right side in this uniform form includes mass and
cancellation in one statement. -/
theorem sum_lagrangeZeroWeight_mul_pow_eq
    (s : Finset ι) (v : ι → K) (hvs : Set.InjOn v s)
    {k : ℕ} (hk : k < s.card) :
    ∑ i ∈ s, lagrangeZeroWeight s v i * (v i) ^ k = (0 : K) ^ k := by
  simpa [lagrangeZeroWeight] using
    sum_lagrangeEvaluationWeight_mul_pow_eq s v 0 hvs hk

/-- Evaluation-at-zero Lagrange weights have total mass one on a nonempty
set of distinct nodes. -/
theorem sum_lagrangeZeroWeight_eq_one
    (s : Finset ι) (v : ι → K) (hvs : Set.InjOn v s)
    (hs : s.Nonempty) :
    ∑ i ∈ s, lagrangeZeroWeight s v i = 1 := by
  simpa using sum_lagrangeZeroWeight_mul_pow_eq s v hvs
    (k := 0) (Finset.card_pos.mpr hs)

/-- Every positive moment below the interpolation degree is cancelled by the
evaluation-at-zero Lagrange weights. -/
theorem sum_lagrangeZeroWeight_mul_pow_eq_zero
    (s : Finset ι) (v : ι → K) (hvs : Set.InjOn v s)
    {k : ℕ} (hkpos : 0 < k) (hk : k < s.card) :
    ∑ i ∈ s, lagrangeZeroWeight s v i * (v i) ^ k = 0 := by
  simpa [zero_pow hkpos.ne'] using
    sum_lagrangeZeroWeight_mul_pow_eq s v hvs hk

end ArbitraryNodes

section GeometricNodes

variable {K : Type*} [Field K]

/-- The Lagrange cardinal weight for evaluation at zero on the geometric
nodes `1, q, ..., q^(s-1)`.  The index is intrinsically bounded by `s`. -/
noncomputable def geometricLagrangeWeight
    (q : K) (s : ℕ) (j : Fin s) : K :=
  lagrangeZeroWeight Finset.univ (fun i : Fin s ↦ q ^ (i : ℕ)) j

/-- Literal finite-product form of the geometric Lagrange weight.  This is
equation `lambda-Lagrange` from the frontier report, over an arbitrary field. -/
theorem geometricLagrangeWeight_eq_product
    (q : K) (s : ℕ) (j : Fin s) :
    geometricLagrangeWeight q s j =
      ∏ l ∈ (Finset.univ : Finset (Fin s)).erase j,
        (-(q ^ (l : ℕ))) / (q ^ (j : ℕ) - q ^ (l : ℕ)) := by
  exact lagrangeZeroWeight_eq_product
    (Finset.univ : Finset (Fin s)) (fun i : Fin s ↦ q ^ (i : ℕ)) j

/-- The geometric weights reproduce all moments below the node count. -/
theorem sum_geometricLagrangeWeight_mul_pow_eq
    (q : K) (s : ℕ)
    (hnodes : Function.Injective (fun j : Fin s ↦ q ^ (j : ℕ)))
    {k : ℕ} (hk : k < s) :
    ∑ j : Fin s, geometricLagrangeWeight q s j *
        q ^ (k * (j : ℕ)) = (0 : K) ^ k := by
  have hmoment := sum_lagrangeZeroWeight_mul_pow_eq
    (K := K) (Finset.univ : Finset (Fin s))
    (fun j : Fin s ↦ q ^ (j : ℕ)) hnodes.injOn hk
  calc
    (∑ j : Fin s, geometricLagrangeWeight q s j *
        q ^ (k * (j : ℕ))) =
        ∑ j : Fin s, geometricLagrangeWeight q s j *
          (q ^ (j : ℕ)) ^ k := by
            apply Finset.sum_congr rfl
            intro j _hj
            congr 1
            rw [← pow_mul]
            congr 1
            exact Nat.mul_comm _ _
    _ = (0 : K) ^ k := by
      simpa [geometricLagrangeWeight] using hmoment

/-- The geometric Lagrange weights have mass one whenever there is at least
one node. -/
theorem sum_geometricLagrangeWeight_eq_one
    (q : K) (s : ℕ)
    (hnodes : Function.Injective (fun j : Fin s ↦ q ^ (j : ℕ)))
    (hs : 0 < s) :
    ∑ j : Fin s, geometricLagrangeWeight q s j = 1 := by
  simpa using sum_geometricLagrangeWeight_mul_pow_eq
    q s hnodes (k := 0) hs

/-- The positive moments `1, ..., s-1` vanish.  In Richardson language these
are precisely the error modes cancelled by `s` samples. -/
theorem sum_geometricLagrangeWeight_mul_pow_eq_zero
    (q : K) (s : ℕ)
    (hnodes : Function.Injective (fun j : Fin s ↦ q ^ (j : ℕ)))
    {k : ℕ} (hkpos : 0 < k) (hk : k < s) :
    ∑ j : Fin s, geometricLagrangeWeight q s j *
        q ^ (k * (j : ℕ)) = 0 := by
  simpa [zero_pow hkpos.ne'] using
    sum_geometricLagrangeWeight_mul_pow_eq q s hnodes hk

/-- The generating polynomial whose coefficient of `X^j` is the geometric
Lagrange weight at the node `q^j`. -/
noncomputable def geometricLagrangeWeightPolynomial
    (q : K) (s : ℕ) : Polynomial K :=
  ∑ j : Fin s,
    Polynomial.C (geometricLagrangeWeight q s j) *
      Polynomial.X ^ (j : ℕ)

/-- Evaluation of the weight-generating polynomial is the corresponding
finite power sum. -/
@[simp] theorem geometricLagrangeWeightPolynomial_eval
    (q x : K) (s : ℕ) :
    (geometricLagrangeWeightPolynomial q s).eval x =
      ∑ j : Fin s, geometricLagrangeWeight q s j * x ^ (j : ℕ) := by
  simp [geometricLagrangeWeightPolynomial]

/-- The weight-generating polynomial has degree strictly below its node
count, without any hypothesis on the base or the weights. -/
theorem geometricLagrangeWeightPolynomial_degree_lt
    (q : K) (s : ℕ) :
    (geometricLagrangeWeightPolynomial q s).degree < s := by
  exact Polynomial.degree_sum_fin_lt
    (fun j : Fin s ↦ geometricLagrangeWeight q s j)

/-- At its `k`-th geometric argument, the weight-generating polynomial has
the moment value `0^k`. -/
theorem geometricLagrangeWeightPolynomial_eval_pow
    (q : K) (s : ℕ)
    (hnodes : Function.Injective (fun j : Fin s ↦ q ^ (j : ℕ)))
    {k : ℕ} (hk : k < s) :
    (geometricLagrangeWeightPolynomial q s).eval (q ^ k) = (0 : K) ^ k := by
  rw [geometricLagrangeWeightPolynomial_eval]
  simpa [pow_mul] using
    sum_geometricLagrangeWeight_mul_pow_eq q s hnodes hk

/-- Distinct geometric nodes imply that the inverse-base Richardson
normalizer does not vanish.  This removes an otherwise repetitive denominator
hypothesis from the Lagrange--Richardson bridge. -/
theorem geometricRootPolynomial_inv_eval_one_ne_zero_of_nodes_injective
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hnodes : Function.Injective
      (fun j : Fin (n + 1) ↦ q ^ (j : ℕ))) :
    (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0 := by
  rw [geometricRootPolynomial_eval_one_ne_zero_iff]
  intro r hr hroot
  have hpow : q ^ (r + 1) = 1 := by
    calc
      q ^ (r + 1) = q ^ (r + 1) * (q⁻¹) ^ (r + 1) := by
        rw [hroot, mul_one]
      _ = (q * q⁻¹) ^ (r + 1) := by rw [mul_pow]
      _ = 1 := by simp [hq]
  let i : Fin (n + 1) := ⟨r + 1, by omega⟩
  let z : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have hiz : i = z := hnodes (by simpa [i, z] using hpow)
  have : r + 1 = 0 := congrArg Fin.val hiz
  omega

/-- The Lagrange weight-generating polynomial on `n+1` geometric nodes is
exactly the normalized forward Richardson polynomial with `n` cancelled
modes. -/
theorem geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hnodes : Function.Injective
      (fun j : Fin (n + 1) ↦ q ^ (j : ℕ))) :
    geometricLagrangeWeightPolynomial q (n + 1) =
      forwardGeometricRichardsonPolynomial q n := by
  have hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0 :=
    geometricRootPolynomial_inv_eval_one_ne_zero_of_nodes_injective
      q hq n hnodes
  have hforwardOne :
      (forwardGeometricRichardsonPolynomial q n).eval 1 = 1 :=
    forwardGeometricRichardsonPolynomial_eval_one q n hden
  have hforwardNe : forwardGeometricRichardsonPolynomial q n ≠ 0 := by
    intro hzero
    rw [hzero] at hforwardOne
    simp at hforwardOne
  have hforwardNatDegree :
      (forwardGeometricRichardsonPolynomial q n).natDegree = n := by
    simpa [forwardGeometricRichardsonPolynomial] using
      normalizedGeometricRootPolynomial_natDegree q⁻¹
        (inv_ne_zero hq) n hden
  have hforwardDegree :
      (forwardGeometricRichardsonPolynomial q n).degree < n + 1 := by
    rw [Polynomial.degree_eq_natDegree hforwardNe, hforwardNatDegree,
      Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.lt_succ_self n
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (Finset.univ : Finset (Fin (n + 1))) hnodes.injOn
    (geometricLagrangeWeightPolynomial_degree_lt q (n + 1))
    hforwardDegree ?_
  intro j _hj
  rw [geometricLagrangeWeightPolynomial_eval_pow q (n + 1) hnodes j.isLt]
  by_cases hjzero : (j : ℕ) = 0
  · simpa [hjzero] using hforwardOne.symm
  · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hjzero
    have hrn : r < n := by
      have hjlt := j.isLt
      rw [hr] at hjlt
      exact Nat.lt_of_succ_lt_succ hjlt
    simpa [hr] using
      (forwardGeometricRichardsonPolynomial_eval_pow_eq_zero
        q hq hrn).symm

/-- First moment beyond the cancelled range.  This is the interpolation
remainder identity `first-uncancelled` from the frontier report, now valid
over every field with distinct geometric nodes and nonzero base. -/
theorem sum_geometricLagrangeWeight_firstUncancelled
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hnodes : Function.Injective
      (fun j : Fin (n + 1) ↦ q ^ (j : ℕ))) :
    ∑ j : Fin (n + 1), geometricLagrangeWeight q (n + 1) j *
        q ^ ((n + 1) * (j : ℕ)) =
      (-1 : K) ^ n * q ^ (n + 1).choose 2 := by
  have hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0 :=
    geometricRootPolynomial_inv_eval_one_ne_zero_of_nodes_injective
      q hq n hnodes
  calc
    (∑ j : Fin (n + 1), geometricLagrangeWeight q (n + 1) j *
        q ^ ((n + 1) * (j : ℕ))) =
        (geometricLagrangeWeightPolynomial q (n + 1)).eval
          (q ^ (n + 1)) := by
            rw [geometricLagrangeWeightPolynomial_eval]
            simp only [pow_mul]
    _ = (forwardGeometricRichardsonPolynomial q n).eval
          (q ^ (n + 1)) := by
            rw [geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
              q hq n hnodes]
    _ = (-1 : K) ^ n * q ^ (n + 1).choose 2 :=
      forwardGeometricRichardsonPolynomial_eval_nextPower_closedForm
        q hq n hden

end GeometricNodes

section QuarterBase

/-- Powers of `1/4` are injective on every finite initial segment. -/
theorem quarter_pow_fin_injective (s : ℕ) :
    Function.Injective
      (fun j : Fin s ↦ (1 / 4 : ℚ) ^ (j : ℕ)) := by
  intro i j hij
  apply Fin.ext
  exact (pow_right_injective₀
    (by norm_num : (0 : ℚ) < 1 / 4)
    (by norm_num : (1 / 4 : ℚ) ≠ 1)) hij

/-- The `q = 1/4` Richardson weights have total mass one. -/
theorem sum_quarterLagrangeWeight_eq_one (s : ℕ) (hs : 0 < s) :
    ∑ j : Fin s, geometricLagrangeWeight (1 / 4 : ℚ) s j = 1 := by
  exact sum_geometricLagrangeWeight_eq_one
    (1 / 4 : ℚ) s (quarter_pow_fin_injective s) hs

/-- At `q = 1/4`, every positive moment below the number of samples is
cancelled exactly. -/
theorem sum_quarterLagrangeWeight_mul_pow_eq_zero
    (s : ℕ) {k : ℕ} (hkpos : 0 < k) (hk : k < s) :
    ∑ j : Fin s, geometricLagrangeWeight (1 / 4 : ℚ) s j *
        (1 / 4 : ℚ) ^ (k * (j : ℕ)) = 0 := by
  exact sum_geometricLagrangeWeight_mul_pow_eq_zero
    (1 / 4 : ℚ) s (quarter_pow_fin_injective s) hkpos hk

/-- At `q = 1/4`, the first power beyond the cancelled range has the exact
signed triangular exponent predicted by the interpolation remainder. -/
theorem sum_quarterLagrangeWeight_firstUncancelled (n : ℕ) :
    ∑ j : Fin (n + 1),
        geometricLagrangeWeight (1 / 4 : ℚ) (n + 1) j *
          (1 / 4 : ℚ) ^ ((n + 1) * (j : ℕ)) =
      (-1 : ℚ) ^ n * (1 / 4 : ℚ) ^ (n + 1).choose 2 := by
  exact sum_geometricLagrangeWeight_firstUncancelled
    (1 / 4 : ℚ) (by norm_num) n (quarter_pow_fin_injective (n + 1))

/-- The generating polynomial of the `n+1` quarter-base Lagrange weights is
the quarter-base forward Richardson polynomial. -/
theorem quarterLagrangeWeightPolynomial_eq_forwardRichardson (n : ℕ) :
    geometricLagrangeWeightPolynomial (1 / 4 : ℚ) (n + 1) =
      forwardGeometricRichardsonPolynomial (1 / 4 : ℚ) n := by
  exact
    geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
      (1 / 4 : ℚ) (by norm_num) n (quarter_pow_fin_injective (n + 1))

end QuarterBase

end Fabius
