import FabiusFunction.LambertPhaseLockedRichardson
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Asymptotic bounds for reciprocal Lambert interpolation rows

For a fixed natural shift `j`, the affine parameter `lambda + j` has the
same order as `lambda` at positive infinity.  Inversion and natural powers
therefore put every shifted reciprocal power on the corresponding
`lambda`-inverse-power scale.

The exact binomial formula for the phase-locked reciprocal Lagrange weights
then shows that every fixed row coefficient with `j <= r` is
`O(lambda ^ r)`.  Summing these coefficient estimates over the fixed finite
row gives the same bound for its total variation.  A power-balancing lemma
then absorbs this growth into any inverse power whose exponent is sufficiently
large.  These estimates are the finite asymptotic input needed before combining
growing Richardson weights with uniform endpoint remainders; no endpoint
expansion is asserted here.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped BigOperators

namespace Fabius

/-! ## Fixed shifted reciprocal scales -/

/-- Adding a fixed natural shift does not change the order of a positive
real parameter at infinity. -/
theorem add_natCast_isTheta_id_atTop (j : ℕ) :
    (fun lambda : ℝ ↦ lambda + (j : ℝ)) =Θ[atTop]
      (fun lambda : ℝ ↦ lambda) := by
  have hnorm : Tendsto (norm ∘ fun lambda : ℝ ↦ lambda) atTop atTop := by
    exact tendsto_norm_atTop_atTop.comp tendsto_id
  exact (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm).isTheta

/-- Every natural power of a fixed shifted reciprocal is asymptotically of
the same order as the corresponding power of `lambda⁻¹`. -/
theorem shiftedReciprocalNode_pow_isTheta_invPow_atTop (j n : ℕ) :
    (fun lambda : ℝ ↦ shiftedReciprocalNode lambda j ^ n) =Θ[atTop]
      (fun lambda : ℝ ↦ lambda⁻¹ ^ n) := by
  simpa only [shiftedReciprocalNode] using
    (add_natCast_isTheta_id_atTop j).inv.pow n

/-- Big-O form of the fixed shifted reciprocal-power comparison. -/
theorem shiftedReciprocalNode_pow_isBigO_invPow_atTop (j n : ℕ) :
    (fun lambda : ℝ ↦ shiftedReciprocalNode lambda j ^ n) =O[atTop]
      (fun lambda : ℝ ↦ lambda⁻¹ ^ n) :=
  (shiftedReciprocalNode_pow_isTheta_invPow_atTop j n).isBigO

/-- Every fixed inverse power is bounded at positive infinity. -/
theorem invPow_isBigO_one_atTop (n : ℕ) :
    (fun lambda : ℝ ↦ lambda⁻¹ ^ n) =O[atTop]
      (fun _lambda : ℝ ↦ (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with lambda hlambda
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_pos (inv_pos.mpr (zero_lt_one.trans_le hlambda)), abs_one, mul_one]
  exact pow_le_one₀ (inv_nonneg.mpr (zero_le_one.trans hlambda))
    (inv_le_one_of_one_le₀ hlambda)

/-- Polynomial growth of order `r` is absorbed by an inverse power of order
`k` with `r + q ≤ k`, leaving an `O(lambda⁻¹ ^ q)` remainder. -/
theorem pow_mul_invPow_isBigO_invPow_atTop
    (r q k : ℕ) (hk : r + q ≤ k) :
    (fun lambda : ℝ ↦ lambda ^ r * lambda⁻¹ ^ k) =O[atTop]
      (fun lambda : ℝ ↦ lambda⁻¹ ^ q) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hproduct :=
    (isBigO_refl (fun lambda : ℝ ↦ lambda⁻¹ ^ q) atTop).mul
      (invPow_isBigO_one_atTop s)
  refine hproduct.congr' ?_ ?_
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with lambda hlambda
    symm
    calc
      lambda ^ r * lambda⁻¹ ^ (r + q + s) =
          (lambda ^ r * lambda⁻¹ ^ r) *
            (lambda⁻¹ ^ q * lambda⁻¹ ^ s) := by
        rw [pow_add, pow_add]
        ring
      _ = lambda⁻¹ ^ q * lambda⁻¹ ^ s := by
        rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero r hlambda), one_mul]
  · exact Filter.Eventually.of_forall fun lambda ↦ by simp

/-! ## Growth of a fixed reciprocal Lagrange row -/

/-- A coefficient in a fixed reciprocal-grid Lagrange row grows at most like
`lambda ^ r`.  The index condition is exactly the range on which the closed
binomial weight formula represents the row. -/
theorem shiftedReciprocalLagrangeWeight_isBigO_pow_atTop
    (r j : ℕ) (hj : j ≤ r) :
    (fun lambda : ℝ ↦ shiftedReciprocalLagrangeWeight lambda r j) =O[atTop]
      (fun lambda : ℝ ↦ lambda ^ r) := by
  have hpow :
      (fun lambda : ℝ ↦ (lambda + (j : ℝ)) ^ r) =O[atTop]
        (fun lambda : ℝ ↦ lambda ^ r) :=
    ((add_natCast_isTheta_id_atTop j).pow r).isBigO
  have hscaled := hpow.const_mul_left
    ((-1 : ℝ) ^ (r - j) / (r.factorial : ℝ) * (r.choose j : ℝ))
  refine hscaled.congr' ?_ (Filter.Eventually.of_forall fun _lambda ↦ rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  exact (shiftedReciprocalLagrangeWeight_eq_choose_of_pos
    lambda hlambda r j hj).symm

/-- After multiplication by a sufficiently high shifted inverse power, one
fixed reciprocal-grid weight leaves the requested inverse-power decay rate. -/
theorem shiftedReciprocalLagrangeWeight_mul_invPow_isBigO_atTop
    (r j k q : ℕ) (hj : j ≤ r) (hk : r + q ≤ k) :
    (fun lambda : ℝ ↦
      shiftedReciprocalLagrangeWeight lambda r j *
        (lambda + (j : ℝ))⁻¹ ^ k) =O[atTop]
      (fun lambda : ℝ ↦ lambda⁻¹ ^ q) := by
  have hproduct :=
    (shiftedReciprocalLagrangeWeight_isBigO_pow_atTop r j hj).mul
      (shiftedReciprocalNode_pow_isBigO_invPow_atTop j k)
  simpa only [shiftedReciprocalNode] using
    hproduct.trans (pow_mul_invPow_isBigO_invPow_atTop r q k hk)

/-- The total variation of a fixed reciprocal-grid Lagrange row is
`O(lambda ^ r)`.  The number of summands is fixed while `lambda → ∞`. -/
theorem sum_norm_shiftedReciprocalLagrangeWeight_isBigO_pow_atTop (r : ℕ) :
    (fun lambda : ℝ ↦
      ∑ j ∈ Finset.range (r + 1),
        ‖shiftedReciprocalLagrangeWeight lambda r j‖) =O[atTop]
      (fun lambda : ℝ ↦ lambda ^ r) := by
  apply IsBigO.sum
  intro j hj
  have hjle : j ≤ r := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  exact (shiftedReciprocalLagrangeWeight_isBigO_pow_atTop r j hjle).norm_left

end Fabius
