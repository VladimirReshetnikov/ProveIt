import FabiusFunction.LagrangeResidualMoments
import FabiusFunction.GeometricLagrangeQMoments

/-!
# Complete-homogeneous form of geometric Lagrange residuals

The universal residual theorem in `LagrangeResidualMoments` expresses every
moment beyond polynomial exactness through a complete homogeneous symmetric
polynomial.  On the geometric nodes

`1, q, ..., q^p`,

that symmetric polynomial is the denominator-free Gaussian coefficient
`gaussianBinomial q (p + r) r`.  This file proves that principal
specialization directly from the adjoining-variable recurrence, then applies
the shared target-zero specialization
`sum_lagrangeEvalWeight_mul_pow_card_add_zero`.

The resulting all-residual formula is valid over an arbitrary field under the
exact finite node-injectivity hypothesis.  Over `ℚ`, the established bridge
from `gaussianBinomial` to the quotient-defined `qBinomial` identifies it with
`geometricLagrangeQMoment_eq_residual_qBinomial`; no second q-binomial
recurrence or interpolation argument is introduced here.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

/-! ## Principal specialization on a geometric alphabet -/

/-- **Principal specialization of the complete homogeneous polynomial.**

On the `p + 1` variables `1, q, ..., q^p`, the degree-`r` complete
homogeneous polynomial is the denominator-free Gaussian coefficient
`[p+r choose r]_q`.  The identity holds in every commutative semiring and at
every value of `q`.

The proof follows the same one-variable adjoining recurrence on both sides;
it does not reproduce the finite q-binomial theorem. -/
theorem completeHomogeneousEvalOn_geometric_range
    {R : Type*} [CommSemiring R]
    (q : R) (p r : ℕ) :
    completeHomogeneousEvalOn (Finset.range (p + 1))
        (fun j : ℕ ↦ q ^ j) r =
      gaussianBinomial q (p + r) r := by
  induction p generalizing r with
  | zero =>
      simp
  | succ p ih =>
      induction r with
      | zero =>
          simp
      | succ r ihr =>
          have hrange :
              insert (p + 1) (Finset.range (p + 1)) =
                Finset.range ((p + 1) + 1) :=
            (Finset.range_succ (p + 1)).symm
          have hrec := completeHomogeneousEvalOn_insert_succ
            (s := Finset.range (p + 1)) (i := p + 1)
            (Finset.not_mem_range_self (p + 1))
            (fun j : ℕ ↦ q ^ j) r
          rw [hrange] at hrec
          rw [show Nat.succ p + 1 = (p + 1) + 1 by omega,
            hrec, ihr, ih (r + 1)]
          have hinner : Nat.succ p + r = p + r + 1 := by omega
          have houter : p + (r + 1) = p + r + 1 := by omega
          have hgoal :
              Nat.succ p + (r + 1) = (p + r + 1) + 1 := by omega
          have hexponent : p + r + 1 - r = p + 1 := by omega
          rw [hinner, houter, hgoal,
            gaussianBinomial_succ_succ, hexponent]
          exact add_comm _ _

/-! ## All residual moments on geometric nodes -/

/-- **All geometric Lagrange residual moments.**

For `p + 1` distinct geometric nodes, the moment in degree `p + 1 + r` is
the first omitted triangular factor times the Gaussian coefficient
`[p+r choose r]_q`.  This is the geometric specialization of
`sum_lagrangeEvalWeight_mul_pow_card_add_zero`, not a second interpolation
proof.
-/
theorem sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial
    {F : Type*} [Field F]
    (q : F) (p r : ℕ)
    (hnode : Set.InjOn (fun k : ℕ ↦ q ^ k)
      (Finset.range (p + 1))) :
    (∑ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k * (q ^ k) ^ (p + 1 + r)) =
      (-1 : F) ^ p * q ^ (p + 1).choose 2 *
        gaussianBinomial q (p + r) r := by
  classical
  have hresidual := sum_lagrangeEvalWeight_mul_pow_card_add_zero
    (Finset.range (p + 1)) (fun k : ℕ ↦ q ^ k) hnode
      (by simp : (Finset.range (p + 1)).Nonempty) r
  calc
    (∑ k ∈ Finset.range (p + 1),
        geometricLagrangeWeight q p k * (q ^ k) ^ (p + 1 + r)) =
        -(∏ k ∈ Finset.range (p + 1), -(q ^ k)) *
          completeHomogeneousEvalOn (Finset.range (p + 1))
            (fun k : ℕ ↦ q ^ k) r := by
      simpa only [geometricLagrangeWeight, Finset.card_range] using
        hresidual
    _ = -(∏ k ∈ Finset.range (p + 1), -(q ^ k)) *
          gaussianBinomial q (p + r) r := by
      rw [completeHomogeneousEvalOn_geometric_range]
    _ = (-1 : F) ^ p * q ^ (p + 1).choose 2 *
          gaussianBinomial q (p + r) r := by
      rw [Finset.prod_neg, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
        Nat.choose_two_right, pow_succ]
      ring

/-- Rational `geometricLagrangeQMoment` form of the denominator-free residual
identity.  Its assumptions are exactly those needed by the established
finite-node injectivity theorem. -/
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

/-- On `0 < q < 1`, the geometric principal specialization is the symmetric
quotient-defined coefficient `[p+r choose p]_q` used by the existing
geometric moment API. -/
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
`geometricLagrangeQMoment_eq_residual_qBinomial` formula (with
`m = p + 1 + r`). -/
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
