import FabiusFunction.GeometricLagrange
import FabiusFunction.GeometricRichardson

/-!
# Product formulas and Richardson polynomials for geometric Lagrange weights

`FabiusFunction.GeometricLagrange` supplies the canonical Lagrange weight

`geometricLagrangeWeight q n k`

for evaluation at zero on the `n + 1` nodes `1, q, ..., q^n`, together with
field-generic moment identities, the first interpolation defect, and
module-valued Richardson exactness.  This module adds only the complementary
structure needed by the frontier reports:

* literal product formulas for the general and geometric weights;
* the polynomial whose coefficients are the geometric weights;
* its exact identification with `forwardGeometricRichardsonPolynomial`;
* the first uncancelled moment in the report's triangular-exponent form; and
* assumption-free `q = 1/4` specializations.

Keeping one canonical weight definition avoids the off-by-one duplication
between a `Fin s` presentation and a `range (n + 1)` presentation.  Bounded
indices are used internally only to package the coefficient polynomial; all
public scalar sums use the canonical range-indexed API.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

noncomputable section

/-! ## Product formulas -/

/-- Literal product form of the canonical Lagrange evaluation weight. -/
theorem lagrangeEvalWeight_eq_product
    {K ι : Type*} [Field K]
    (s : Finset ι) (v : ι → K) (x : K) (i : ι) :
    lagrangeEvalWeight s v x i =
      ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
  classical
  rw [lagrangeEvalWeight, Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  simp [Lagrange.basisDivisor, div_eq_mul_inv, mul_comm]

/-- Literal product form of the geometric evaluation-at-zero weight on
`1, q, ..., q^n`.  No distinct-node hypothesis is needed for the identity
because Mathlib's Lagrange basis is total. -/
theorem geometricLagrangeWeight_eq_product
    {K : Type*} [Field K] (q : K) (n k : ℕ) :
    geometricLagrangeWeight q n k =
      ∏ j ∈ (Finset.range (n + 1)).erase k,
        (-(q ^ j)) / (q ^ k - q ^ j) := by
  rw [geometricLagrangeWeight,
    lagrangeEvalWeight_eq_product]
  simp only [zero_sub]

/-! ## The coefficient polynomial -/

/-- The polynomial whose coefficient of `X^k` is the canonical geometric
Lagrange weight at the node `q^k`, for `0 ≤ k ≤ n`. -/
noncomputable def geometricLagrangeWeightPolynomial
    {K : Type*} [Field K] (q : K) (n : ℕ) : Polynomial K :=
  ∑ k : Fin (n + 1),
    Polynomial.C (geometricLagrangeWeight q n (k : ℕ)) *
      Polynomial.X ^ (k : ℕ)

/-- Evaluation of the weight polynomial is its finite coefficient sum. -/
@[simp] theorem geometricLagrangeWeightPolynomial_eval
    {K : Type*} [Field K] (q x : K) (n : ℕ) :
    (geometricLagrangeWeightPolynomial q n).eval x =
      ∑ k : Fin (n + 1),
        geometricLagrangeWeight q n (k : ℕ) * x ^ (k : ℕ) := by
  simp [geometricLagrangeWeightPolynomial]

/-- The weight polynomial has degree strictly below its `n + 1` coefficient
slots, independently of whether the geometric nodes are distinct. -/
theorem geometricLagrangeWeightPolynomial_degree_lt
    {K : Type*} [Field K] (q : K) (n : ℕ) :
    (geometricLagrangeWeightPolynomial q n).degree < n + 1 := by
  exact Polynomial.degree_sum_fin_lt
    (fun k : Fin (n + 1) ↦ geometricLagrangeWeight q n (k : ℕ))

/-- At every geometric interpolation node through order `n`, the weight
polynomial has the corresponding evaluation-at-zero moment `0^d`. -/
theorem geometricLagrangeWeightPolynomial_eval_pow
    {K : Type*} [Field K] (q : K) (n d : ℕ)
    (hnodes : Set.InjOn (fun k : ℕ ↦ q ^ k) (Finset.range (n + 1)))
    (hd : d ≤ n) :
    (geometricLagrangeWeightPolynomial q n).eval (q ^ d) =
      (0 : K) ^ d := by
  rw [geometricLagrangeWeightPolynomial_eval,
    Fin.sum_univ_eq_sum_range]
  simpa [pow_mul, Nat.mul_comm] using
    sum_geometricLagrangeWeight_mul_pow q n d hnodes hd

/-! ## Identification with the Richardson filter -/

/-- Distinct forward geometric nodes and a nonzero base imply that the
inverse-base Richardson normalizer is nonzero. -/
theorem geometricRootPolynomial_inv_eval_one_ne_zero_of_nodes_injective
    {K : Type*} [Field K] (q : K) (hq : q ≠ 0) (n : ℕ)
    (hnodes : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (n + 1))) :
    (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0 := by
  rw [geometricRootPolynomial_eval_one_ne_zero_iff]
  intro r hr hroot
  have hpow : q ^ (r + 1) = 1 := by
    calc
      q ^ (r + 1) = q ^ (r + 1) * (q⁻¹) ^ (r + 1) := by
        rw [hroot, mul_one]
      _ = (q * q⁻¹) ^ (r + 1) := by rw [mul_pow]
      _ = 1 := by simp [hq]
  have hindex : r + 1 = 0 := hnodes
    (Finset.mem_range.mpr (by omega))
    (Finset.mem_range.mpr (Nat.zero_lt_succ n))
    (by simpa using hpow)
  omega

/-- The coefficient polynomial of the `n + 1` geometric Lagrange weights is
exactly the normalized forward Richardson polynomial with `n` cancelled
modes. -/
theorem geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
    {K : Type*} [Field K] (q : K) (hq : q ≠ 0) (n : ℕ)
    (hnodes : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (n + 1))) :
    geometricLagrangeWeightPolynomial q n =
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
    (Finset.range (n + 1)) hnodes
    (geometricLagrangeWeightPolynomial_degree_lt q n)
    hforwardDegree ?_
  intro d hd
  have hdn : d ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  rw [geometricLagrangeWeightPolynomial_eval_pow q n d hnodes hdn]
  by_cases hdzero : d = 0
  · subst d
    simpa using hforwardOne.symm
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdzero
    have hrn : r < n := by omega
    simpa using
      (forwardGeometricRichardsonPolynomial_eval_pow_eq_zero
        q hq hrn).symm

/-- First moment beyond the cancelled range, in the exact signed triangular
form used by the frontier report. -/
theorem sum_geometricLagrangeWeight_firstUncancelled
    {K : Type*} [Field K] (q : K) (n : ℕ)
    (hnodes : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (n + 1))) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k * q ^ ((n + 1) * k)) =
      (-1 : K) ^ n * q ^ (n + 1).choose 2 := by
  simpa [pow_mul, Nat.choose_two_right, Nat.mul_comm] using
    sum_geometricLagrangeWeight_mul_pow_succ q n hnodes

/-! ## The quarter-base specialization -/

/-- Powers of `1/4` are injective on every finite initial range. -/
theorem quarter_pow_injOn (n : ℕ) :
    Set.InjOn (fun k : ℕ ↦ (1 / 4 : ℚ) ^ k)
      (Finset.range (n + 1)) := by
  intro i _hi j _hj hij
  exact pow_right_injective₀
    (by norm_num : (0 : ℚ) < 1 / 4)
    (by norm_num : (1 / 4 : ℚ) ≠ 1) hij

/-- The `q = 1/4` weights on `n + 1` nodes have total mass one. -/
theorem sum_quarterLagrangeWeight_eq_one (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight (1 / 4 : ℚ) n k) = 1 := by
  exact sum_geometricLagrangeWeight
    (1 / 4 : ℚ) n (quarter_pow_injOn n)

/-- At `q = 1/4`, every positive moment through degree `n` is cancelled. -/
theorem sum_quarterLagrangeWeight_mul_pow_eq_zero
    (n d : ℕ) (hdpos : 0 < d) (hd : d ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight (1 / 4 : ℚ) n k *
        ((1 / 4 : ℚ) ^ k) ^ d) = 0 := by
  exact sum_geometricLagrangeWeight_mul_pow_eq_zero
    (1 / 4 : ℚ) n d (quarter_pow_injOn n) hdpos hd

/-- At `q = 1/4`, the first uncancelled moment has its exact signed
triangular exponent. -/
theorem sum_quarterLagrangeWeight_firstUncancelled (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight (1 / 4 : ℚ) n k *
        (1 / 4 : ℚ) ^ ((n + 1) * k)) =
      (-1 : ℚ) ^ n * (1 / 4 : ℚ) ^ (n + 1).choose 2 := by
  exact sum_geometricLagrangeWeight_firstUncancelled
    (1 / 4 : ℚ) n (quarter_pow_injOn n)

/-- The quarter-base weight polynomial is the corresponding normalized
forward Richardson polynomial. -/
theorem quarterLagrangeWeightPolynomial_eq_forwardRichardson (n : ℕ) :
    geometricLagrangeWeightPolynomial (1 / 4 : ℚ) n =
      forwardGeometricRichardsonPolynomial (1 / 4 : ℚ) n := by
  exact
    geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
      (1 / 4 : ℚ) (by norm_num) n (quarter_pow_injOn n)

end

end Fabius
