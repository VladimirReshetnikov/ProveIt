import FabiusFunction.GeometricCompleteHomogeneous
import FabiusFunction.LagrangeResidualMoments

/-!
# All residual moments on a geometric grid

This module closes the finite algebraic core of geometric Richardson
extrapolation.  An arbitrary row of weights which reproduces evaluation at
zero through degree `p` has every positive geometric moment

`sum k=0..p, w_k (q^k)^m
  = (-1)^p q^((p+1 choose 2)) gaussianBinomial q (m-1) p`.

The foundational theorem is valid over every commutative ring.  It assumes
only the low moments themselves: the nodes may repeat, and no division,
nonzeroness, or distinctness is used.  The proof combines the universal
Lagrange residual identity with the principal specialization
`h_r(1,q,...,q^p) = gaussianBinomial q (r+p) p`.

Field-valued Lagrange rows are then immediate corollaries.  A still more
general dilation theorem treats nodes `c * q^k` for arbitrary `c`; the usual
shifted block `q^(start+k)` is its geometric specialization.

## Main results

* `sum_weight_mul_geometric_pow_succ_add` is the generic all-residual theorem
  in offset degree `p + 1 + r`.
* `sum_weight_mul_geometric_pow_of_pos` packages cancellations and all
  residual degrees in one formula for `m > 0`.
* `sum_weight_mul_scaled_geometric_pow_succ_add` and
  `sum_weight_mul_scaled_geometric_pow_of_pos` assume exactness directly on
  an arbitrarily scaled row, without assuming the scale is nonzero.
* `sum_geometricLagrangeWeight_mul_pow_of_pos` and
  `sum_geometricLagrangeWeight_mul_shifted_pow_of_pos` are the Lagrange and
  shifted-grid forms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

noncomputable section

private theorem neg_prod_zero_sub_geometric
    {R : Type*} [CommRing R] (q : R) (p : ℕ) :
    -(∏ k ∈ Finset.range (p + 1), ((0 : R) - q ^ k)) =
      (-1 : R) ^ p * q ^ ((p + 1).choose 2) := by
  simp only [zero_sub]
  rw [Finset.prod_neg, Finset.card_range,
    Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    ← Nat.choose_two_right, pow_succ]
  ring

private theorem neg_prod_zero_sub_scaled_geometric
    {R : Type*} [CommRing R] (c q : R) (p : ℕ) :
    -(∏ k ∈ Finset.range (p + 1), ((0 : R) - c * q ^ k)) =
      (-1 : R) ^ p * c ^ (p + 1) * q ^ ((p + 1).choose 2) := by
  simp only [zero_sub]
  rw [Finset.prod_neg, Finset.card_range,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    ← Nat.choose_two_right, pow_succ]
  ring

/-- **All higher moments of an exact geometric row.**

If `weight` reproduces evaluation at zero through degree `p`, its moment in
degree `p + 1 + r` is one denominator-free Gaussian coefficient.  The
statement holds over every commutative ring, including the zero ring, and
requires neither distinct nodes nor division. -/
theorem sum_weight_mul_geometric_pow_succ_add
    {R : Type*} [CommRing R]
    (q : R) (p : ℕ) (weight : ℕ → R)
    (hmoment : ∀ d ≤ p,
      ∑ k ∈ Finset.range (p + 1),
        weight k * (q ^ k) ^ d = (0 : R) ^ d)
    (r : ℕ) :
    (∑ k ∈ Finset.range (p + 1),
      weight k * (q ^ k) ^ (p + 1 + r)) =
      (-1 : R) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (p + r) p := by
  have hmoment' : ∀ d < (Finset.range (p + 1)).card,
      ∑ k ∈ Finset.range (p + 1),
        weight k * (q ^ k) ^ d = (0 : R) ^ d := by
    intro d hd
    exact hmoment d (by simpa only [Finset.card_range, Nat.lt_succ_iff] using hd)
  have hres := sum_weight_mul_pow_card_add
    (Finset.range (p + 1)) weight (fun k : ℕ ↦ q ^ k) 0 hmoment' r
  have hdegree : 0 < p + 1 + r := by omega
  calc
    (∑ k ∈ Finset.range (p + 1),
        weight k * (q ^ k) ^ (p + 1 + r)) =
        (0 : R) ^ (p + 1 + r) -
          (∏ k ∈ Finset.range (p + 1), ((0 : R) - q ^ k)) *
            completeHomogeneousEvalAt (Finset.range (p + 1))
              (fun k : ℕ ↦ q ^ k) 0 r := by
      simpa only [Finset.card_range] using hres
    _ = (-1 : R) ^ p * q ^ ((p + 1).choose 2) *
          gaussianBinomial q (p + r) p := by
      rw [zero_pow hdegree.ne', zero_sub, ← neg_mul,
        neg_prod_zero_sub_geometric,
        completeHomogeneousEvalAt_zero,
        completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial,
        Nat.add_comm r p]

/-- **Every positive geometric moment of an exact row.**

Above-diagonal vanishing of `gaussianBinomial` incorporates all cancelled
degrees `1, ..., p`; the same formula then gives every surviving residual
degree.  Degree zero is intentionally left in the normalization hypothesis,
because its value is one rather than the displayed positive-degree form. -/
theorem sum_weight_mul_geometric_pow_of_pos
    {R : Type*} [CommRing R]
    (q : R) (p : ℕ) (weight : ℕ → R)
    (hmoment : ∀ d ≤ p,
      ∑ k ∈ Finset.range (p + 1),
        weight k * (q ^ k) ^ d = (0 : R) ^ d)
    (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range (p + 1),
      weight k * (q ^ k) ^ m) =
      (-1 : R) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (m - 1) p := by
  by_cases hmp : m ≤ p
  · rw [hmoment m hmp, zero_pow hm.ne',
      gaussianBinomial_eq_zero_of_lt q (by omega : m - 1 < p),
      mul_zero]
  · have hpm : p < m := Nat.lt_of_not_ge hmp
    let r := m - (p + 1)
    have hdegree : p + 1 + r = m := by
      dsimp only [r]
      omega
    have hindex : p + r = m - 1 := by
      dsimp only [r]
      omega
    simpa only [hdegree, hindex] using
      sum_weight_mul_geometric_pow_succ_add q p weight hmoment r

/-- **All higher moments of a scaled exact geometric row.**

Exactness is assumed directly on the displayed nodes `c * q ^ k`.  This is
strictly more general than exactness before scaling when `c` is zero or a
zero divisor.  The scale contributes the homogeneous factor
`c ^ (p + 1 + r)` and need not be nonzero. -/
theorem sum_weight_mul_scaled_geometric_pow_succ_add
    {R : Type*} [CommRing R]
    (c q : R) (p : ℕ) (weight : ℕ → R)
    (hmoment : ∀ d ≤ p,
      ∑ k ∈ Finset.range (p + 1),
        weight k * (c * q ^ k) ^ d = (0 : R) ^ d)
    (r : ℕ) :
    (∑ k ∈ Finset.range (p + 1),
      weight k * (c * q ^ k) ^ (p + 1 + r)) =
      c ^ (p + 1 + r) *
        ((-1 : R) ^ p * q ^ ((p + 1).choose 2) *
          gaussianBinomial q (p + r) p) := by
  have hmoment' : ∀ d < (Finset.range (p + 1)).card,
      ∑ k ∈ Finset.range (p + 1),
        weight k * (c * q ^ k) ^ d = (0 : R) ^ d := by
    intro d hd
    exact hmoment d (by simpa only [Finset.card_range, Nat.lt_succ_iff] using hd)
  have hres := sum_weight_mul_pow_card_add
    (Finset.range (p + 1)) weight (fun k : ℕ ↦ c * q ^ k) 0 hmoment' r
  have hdegree : 0 < p + 1 + r := by omega
  calc
    (∑ k ∈ Finset.range (p + 1),
        weight k * (c * q ^ k) ^ (p + 1 + r)) =
        (0 : R) ^ (p + 1 + r) -
          (∏ k ∈ Finset.range (p + 1),
            ((0 : R) - c * q ^ k)) *
            completeHomogeneousEvalAt (Finset.range (p + 1))
              (fun k : ℕ ↦ c * q ^ k) 0 r := by
      simpa only [Finset.card_range] using hres
    _ = c ^ (p + 1 + r) *
          ((-1 : R) ^ p * q ^ ((p + 1).choose 2) *
            gaussianBinomial q (p + r) p) := by
      rw [zero_pow hdegree.ne', zero_sub, ← neg_mul,
        neg_prod_zero_sub_scaled_geometric,
        completeHomogeneousEvalAt_zero,
        completeHomogeneousEvalOn_range,
        completeHomogeneousEval_scaled_geometric,
        Nat.add_comm r p, pow_add]
      ring

/-- Every positive moment of a scaled exact geometric row.  Exactness is
assumed after scaling, so the result remains maximal at nonunits and zero
divisors. -/
theorem sum_weight_mul_scaled_geometric_pow_of_pos
    {R : Type*} [CommRing R]
    (c q : R) (p : ℕ) (weight : ℕ → R)
    (hmoment : ∀ d ≤ p,
      ∑ k ∈ Finset.range (p + 1),
        weight k * (c * q ^ k) ^ d = (0 : R) ^ d)
    (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range (p + 1),
      weight k * (c * q ^ k) ^ m) =
      c ^ m * ((-1 : R) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (m - 1) p) := by
  by_cases hmp : m ≤ p
  · rw [hmoment m hmp, zero_pow hm.ne',
      gaussianBinomial_eq_zero_of_lt q (by omega : m - 1 < p),
      mul_zero, mul_zero]
  · have hpm : p < m := Nat.lt_of_not_ge hmp
    let r := m - (p + 1)
    have hdegree : p + 1 + r = m := by
      dsimp only [r]
      omega
    have hindex : p + r = m - 1 := by
      dsimp only [r]
      omega
    simpa only [hdegree, hindex] using
      sum_weight_mul_scaled_geometric_pow_succ_add
        c q p weight hmoment r

/-- Offset-degree form of the all-order residual formula for the geometric
Lagrange row.  Distinctness enters only to supply the low moments. -/
theorem sum_geometricLagrangeWeight_mul_pow_succ_add
    {F : Type*} [Field F]
    (q : F) (p r : ℕ)
    (hnode : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (p + 1))) :
    (∑ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k * (q ^ k) ^ (p + 1 + r)) =
      (-1 : F) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (p + r) p := by
  exact sum_weight_mul_geometric_pow_succ_add q p
    (geometricLagrangeWeight q p)
    (fun d hd ↦ sum_geometricLagrangeWeight_mul_pow q p d hnode hd) r

/-- Every positive moment of the geometric Lagrange row is one recursive
Gaussian coefficient.  This single formula includes all cancelled moments
and all higher residual moments. -/
theorem sum_geometricLagrangeWeight_mul_pow_of_pos
    {F : Type*} [Field F]
    (q : F) (p m : ℕ)
    (hnode : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (p + 1)))
    (hm : 0 < m) :
    (∑ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k * (q ^ k) ^ m) =
      (-1 : F) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (m - 1) p := by
  exact sum_weight_mul_geometric_pow_of_pos q p
    (geometricLagrangeWeight q p)
    (fun d hd ↦ sum_geometricLagrangeWeight_mul_pow q p d hnode hd) m hm

/-- Every positive moment after a common dilation of the samples in a
geometric Lagrange row.  No nonzeroness condition is imposed on `c`. -/
theorem sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos
    {F : Type*} [Field F]
    (c q : F) (p m : ℕ)
    (hnode : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (p + 1)))
    (hm : 0 < m) :
    (∑ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k * (c * q ^ k) ^ m) =
      c ^ m * ((-1 : F) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (m - 1) p) := by
  have hscaled : ∀ d ≤ p,
      ∑ k ∈ Finset.range (p + 1),
        geometricLagrangeWeight q p k * (c * q ^ k) ^ d =
          (0 : F) ^ d := by
    intro d hd
    calc
      (∑ k ∈ Finset.range (p + 1),
          geometricLagrangeWeight q p k * (c * q ^ k) ^ d) =
          c ^ d * ∑ k ∈ Finset.range (p + 1),
            geometricLagrangeWeight q p k * (q ^ k) ^ d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [mul_pow]
        ring
      _ = c ^ d * (0 : F) ^ d := by
        rw [sum_geometricLagrangeWeight_mul_pow q p d hnode hd]
      _ = (0 : F) ^ d := by
        cases d <;> simp
  exact sum_weight_mul_scaled_geometric_pow_of_pos c q p
    (geometricLagrangeWeight q p) hscaled m hm

/-- Shifted-block form of every positive geometric Lagrange moment.  The
shift contributes exactly `q ^ (start * m)` and requires no additional
hypothesis on `q`. -/
theorem sum_geometricLagrangeWeight_mul_shifted_pow_of_pos
    {F : Type*} [Field F]
    (q : F) (p start m : ℕ)
    (hnode : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (p + 1)))
    (hm : 0 < m) :
    (∑ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k * (q ^ (start + k)) ^ m) =
      (-1 : F) ^ p *
        q ^ (start * m + (p + 1).choose 2) *
          gaussianBinomial q (m - 1) p := by
  calc
    (∑ k ∈ Finset.range (p + 1),
        geometricLagrangeWeight q p k * (q ^ (start + k)) ^ m) =
        ∑ k ∈ Finset.range (p + 1),
          geometricLagrangeWeight q p k *
            (q ^ start * q ^ k) ^ m := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [pow_add]
    _ = (q ^ start) ^ m *
          ((-1 : F) ^ p * q ^ ((p + 1).choose 2) *
            gaussianBinomial q (m - 1) p) :=
      sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos
        (q ^ start) q p m hnode hm
    _ = (-1 : F) ^ p *
          q ^ (start * m + (p + 1).choose 2) *
            gaussianBinomial q (m - 1) p := by
      rw [← pow_mul]
      calc
        q ^ (start * m) *
              ((-1 : F) ^ p * q ^ ((p + 1).choose 2) *
                gaussianBinomial q (m - 1) p) =
            (-1 : F) ^ p *
              (q ^ (start * m) * q ^ ((p + 1).choose 2)) *
                gaussianBinomial q (m - 1) p := by ring
        _ = (-1 : F) ^ p *
              q ^ (start * m + (p + 1).choose 2) *
                gaussianBinomial q (m - 1) p := by
          rw [pow_add]

end

end Fabius
