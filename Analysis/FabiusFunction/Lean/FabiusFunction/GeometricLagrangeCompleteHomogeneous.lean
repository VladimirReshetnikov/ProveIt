import FabiusFunction.GeometricResidualMoments
import FabiusFunction.GeometricLagrangeQMoments

/-!
# Compatibility bridges for geometric complete-homogeneous residuals

The structural proofs behind this file now live in two canonical modules:

* `GeometricCompleteHomogeneous` proves the principal specialization
  `h_r(1, q, ..., q^p) = gaussianBinomial q (p + r) p` over an arbitrary
  commutative semiring; and
* `GeometricResidualMoments` combines that specialization with the universal
  residual theorem, first for any exact row over a commutative ring and then
  for geometric Lagrange weights over a field.

This module retains the report-facing declaration names introduced before
that separation and supplies the rational bridge to the quotient-defined
`qBinomial`.  Every proof below is consequently a thin specialization of a
canonical theorem: there is no second symmetric-function induction, product
calculation, or interpolation argument.

The canonical residual theorem uses the lower index `p`, whereas the original
report-facing API used the complementary presentation `[p+r choose r]_q`.
`GeometricCompleteHomogeneous` now proves both principal-specialization
orientations and derives their equality as the denominator-free symmetry
theorem `gaussianBinomial_add_symm`.  The compatibility declarations can
therefore retain their original types without replaying any structural proof.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## Report-facing aliases of the canonical algebraic results -/

/-- Report-facing range-indexed form of the geometric principal
specialization.  The proof is owned by `GeometricCompleteHomogeneous`. -/
theorem completeHomogeneousEvalOn_geometric_range
    {R : Type*} [CommSemiring R]
    (q : R) (p r : ℕ) :
    completeHomogeneousEvalOn (Finset.range (p + 1))
        (fun j : ℕ ↦ q ^ j) r =
      gaussianBinomial q (p + r) r :=
  completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree
    q p r

/-- Report-facing offset-degree form of all geometric Lagrange residual
moments.  Distinctness is used only by the canonical theorem to obtain the
low moments of the Lagrange row. -/
theorem sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial
    {F : Type*} [Field F]
    (q : F) (p r : ℕ)
    (hnode : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (p + 1))) :
    (∑ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k * (q ^ k) ^ (p + 1 + r)) =
      (-1 : F) ^ p * q ^ (p + 1).choose 2 *
        gaussianBinomial q (p + r) r := by
  calc
    (∑ k ∈ Finset.range (p + 1),
        geometricLagrangeWeight q p k * (q ^ k) ^ (p + 1 + r)) =
        (-1 : F) ^ p * q ^ (p + 1).choose 2 *
          gaussianBinomial q (p + r) p :=
      sum_geometricLagrangeWeight_mul_pow_succ_add q p r hnode
    _ = (-1 : F) ^ p * q ^ (p + 1).choose 2 *
          gaussianBinomial q (p + r) r := by
      rw [gaussianBinomial_add_symm q p r]

/-! ## Rational bridges -/

/-- Rational `geometricLagrangeQMoment` form of the denominator-free
residual identity.  Its assumptions are exactly those needed by the
established finite-node injectivity theorem. -/
theorem geometricLagrangeQMoment_eq_residual_gaussianBinomial
    (q : ℚ) (hq : q ≠ 0) (p r : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) :
    geometricLagrangeQMoment q p (p + 1 + r) =
      (-1 : ℚ) ^ p * q ^ (p + 1).choose 2 *
        gaussianBinomial q (p + r) r := by
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  simpa only [geometricLagrangeQMoment] using
    sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial
      q p r hnodes

/-- On `0 < q < 1`, geometric principal specialization is the
quotient-defined coefficient `[p+r choose p]_q` used by the rational moment
API. -/
theorem completeHomogeneousEvalOn_geometric_range_eq_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (p r : ℕ) :
    completeHomogeneousEvalOn (Finset.range (p + 1))
        (fun j : ℕ ↦ q ^ j) r =
      qBinomial (p + r) p q := by
  rw [completeHomogeneousEvalOn_geometric_range,
    gaussianBinomial_eq_qBinomial_of_pos_of_lt_one
      q hqpos hqone (p + r) r]
  calc
    qBinomial (p + r) r q =
        qBinomial (p + r) (p + r - r) q :=
      (qBinomial_symm q (by omega : r ≤ p + r)).symm
    _ = qBinomial (p + r) p q := by
      rw [show p + r - r = p by omega]

/-- The complete-homogeneous derivation specializes to exactly the existing
`geometricLagrangeQMoment_eq_residual_qBinomial` formula, with
`m = p + 1 + r`. -/
theorem geometricLagrangeQMoment_eq_residual_qBinomial_via_completeHomogeneous
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (p r : ℕ) :
    geometricLagrangeQMoment q p (p + 1 + r) =
      (-1 : ℚ) ^ p * q ^ (p + 1).choose 2 *
        qBinomial (p + r) p q := by
  have hPochhammer : qPochhammer q q p ≠ 0 :=
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne'
  rw [geometricLagrangeQMoment_eq_residual_gaussianBinomial
      q hqpos.ne' p r hPochhammer,
    ← completeHomogeneousEvalOn_geometric_range q p r,
    completeHomogeneousEvalOn_geometric_range_eq_qBinomial
      q hqpos hqone p r]

end

end Fabius
