import FabiusFunction.FabiusLambertPhaseLockedPullback
import FabiusFunction.CompleteHomogeneousAsymptotics
import FabiusFunction.LambertReciprocalAsymptotics

/-!
# Phase-locked extraction of the periodic Fabius endpoint term

The exact lower-Lambert nodes `lambertPhaseLockedNode lambda j` freeze every
one-periodic saddle coefficient at the common phase `lambda`.  This module
combines the resulting samples with the reciprocal Lagrange row of order
`r`.  The row has mass one and cancels the first `r` inverse-phase powers,
so the transformed observable recovers `negativeLaplacePsi lambda` with a
high-order algebraic error.

The definitions below are total for every real `lambda`.  Analytic estimates
are stated at `Filter.atTop`, where positivity of all shifted denominators and
membership in the strict lower-Lambert branch hold eventually.
-/

set_option autoImplicit false

open scoped BigOperators

open Filter Set Asymptotics

namespace Fabius

open Finset

noncomputable section

/-! ## Estimator and exact residual terms -/

/-- The phase-locked logarithmic sample after subtracting the nonperiodic
Wikipedia/Lambert main term. -/
noncomputable def fabiusPhaseLockedReducedSample
    (F : BoundedFabius) (lambda : ℝ) (j : ℕ) : ℝ :=
  Real.log (fabiusReal F (lambertPhaseLockedNode lambda j)) -
    fabiusWikipediaLambertMain (lambertPhaseLockedNode lambda j)

/-- Reciprocal-Lagrange extrapolation of the reduced phase-locked samples. -/
noncomputable def fabiusPhaseLockedPeriodicEstimator
    (F : BoundedFabius) (r : ℕ) (lambda : ℝ) : ℝ :=
  ∑ j ∈ range (r + 1),
    shiftedReciprocalLagrangeWeight lambda r j *
      fabiusPhaseLockedReducedSample F lambda j

/-- The residual contribution with offset `n` after the first `r` inverse
powers have been cancelled.  It is the exact higher reciprocal-grid moment
times the saddle coefficient of index `r + 1 + n`. -/
noncomputable def fabiusPhaseLockedResidualTerm
    (r n : ℕ) (lambda : ℝ) : ℝ :=
  (-1 : ℝ) ^ r *
    (∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) *
    completeHomogeneousEvalOn (range (r + 1))
      (fun j ↦ (lambda + (j : ℝ))⁻¹) n *
    fabiusSaddleLogCoefficient (r + 1 + n) lambda

/-- The first `S` exact residual contributions of the phase-locked
extrapolator. -/
noncomputable def fabiusPhaseLockedResidualPartialSum
    (r S : ℕ) (lambda : ℝ) : ℝ :=
  ∑ n ∈ range S, fabiusPhaseLockedResidualTerm r n lambda

private noncomputable def fabiusPhaseLockedNodeRemainder
    (F : BoundedFabius) (N : ℕ) (lambda : ℝ) (j : ℕ) : ℝ :=
  fabiusPhaseLockedReducedSample F lambda j - negativeLaplacePsi lambda -
    ∑ k ∈ range N,
      (lambda + (j : ℝ))⁻¹ ^ k * fabiusSaddleLogCoefficient k lambda

private noncomputable def fabiusPhaseLockedWeightedRemainder
    (F : BoundedFabius) (r N : ℕ) (lambda : ℝ) : ℝ :=
  ∑ j ∈ range (r + 1),
    shiftedReciprocalLagrangeWeight lambda r j *
      fabiusPhaseLockedNodeRemainder F N lambda j

private noncomputable def fabiusPhaseLockedCoefficientMoment
    (r N : ℕ) (lambda : ℝ) : ℝ :=
  ∑ k ∈ range N,
    fabiusSaddleLogCoefficient k lambda *
      (∑ j ∈ range (r + 1),
        shiftedReciprocalLagrangeWeight lambda r j *
          (lambda + (j : ℝ))⁻¹ ^ k)

/-! ## Structural identities -/

/-- The single-node remainder is controlled at every order by the shifted
inverse phase. -/
private theorem fabiusPhaseLockedNodeRemainder_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (j N : ℕ) :
    (fun lambda : ℝ => fabiusPhaseLockedNodeRemainder F N lambda j)
      =O[atTop] (fun lambda : ℝ => (lambda + (j : ℝ))⁻¹ ^ N) := by
  simpa only [fabiusPhaseLockedNodeRemainder,
    fabiusPhaseLockedReducedSample, sub_sub] using
      log_fabius_phaseLockedNode_sub_WikipediaLambertExpansion_isBigO
        F hF j N

/-- Exact decomposition of the extrapolation error into the finite saddle
coefficient moments and the weighted analytic remainder. -/
private theorem fabiusPhaseLockedPeriodicEstimator_sub_periodic_eq
    (F : BoundedFabius) (r N : ℕ) (lambda : ℝ) :
    fabiusPhaseLockedPeriodicEstimator F r lambda - negativeLaplacePsi lambda =
      fabiusPhaseLockedCoefficientMoment r N lambda +
        fabiusPhaseLockedWeightedRemainder F r N lambda := by
  let w : ℕ → ℝ := fun j =>
    shiftedReciprocalLagrangeWeight lambda r j
  let Y : ℕ → ℝ := fun j =>
    fabiusPhaseLockedReducedSample F lambda j
  let P : ℕ → ℝ := fun j =>
    ∑ k ∈ range N,
      (lambda + (j : ℝ))⁻¹ ^ k * fabiusSaddleLogCoefficient k lambda
  let R : ℕ → ℝ := fun j =>
    fabiusPhaseLockedNodeRemainder F N lambda j
  have hmass : (∑ j ∈ range (r + 1), w j) = 1 := by
    simpa only [w] using
      (sum_shiftedReciprocalLagrangeWeight_eq_one lambda r)
  have hsample (j : ℕ) : Y j - negativeLaplacePsi lambda = P j + R j := by
    simp only [Y, P, R, fabiusPhaseLockedNodeRemainder]
    ring
  have hpartial :
      (∑ j ∈ range (r + 1), w j * P j) =
        fabiusPhaseLockedCoefficientMoment r N lambda := by
    simp only [P, fabiusPhaseLockedCoefficientMoment]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    fabiusPhaseLockedPeriodicEstimator F r lambda - negativeLaplacePsi lambda =
        (∑ j ∈ range (r + 1), w j * Y j) -
          (∑ j ∈ range (r + 1), w j) * negativeLaplacePsi lambda := by
            simp only [fabiusPhaseLockedPeriodicEstimator, w, Y, hmass]
            ring
    _ = ∑ j ∈ range (r + 1),
          w j * (Y j - negativeLaplacePsi lambda) := by
            simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = ∑ j ∈ range (r + 1), w j * (P j + R j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hsample j]
    _ = (∑ j ∈ range (r + 1), w j * P j) +
          ∑ j ∈ range (r + 1), w j * R j := by
            simp_rw [mul_add, Finset.sum_add_distrib]
    _ = fabiusPhaseLockedCoefficientMoment r N lambda +
          fabiusPhaseLockedWeightedRemainder F r N lambda := by
            rw [hpartial]
            rfl

/-! ## Quantitative residual estimates -/

private theorem fabiusSaddleLogCoefficient_isBigO_one_atTop (k : ℕ) :
    (fun lambda : ℝ => fabiusSaddleLogCoefficient k lambda) =O[atTop]
      (fun _lambda : ℝ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    (isBounded_range_fabiusSaddleLogCoefficient k).exists_norm_le
  apply IsBigO.of_bound C
  filter_upwards with lambda
  simpa only [norm_one, mul_one] using
    hC (fabiusSaddleLogCoefficient k lambda) ⟨lambda, rfl⟩

private theorem prod_shiftedReciprocal_isBigO_invPow_atTop (r : ℕ) :
    (fun lambda : ℝ =>
      ∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) =O[atTop]
        (fun lambda : ℝ => lambda⁻¹ ^ (r + 1)) := by
  have hprod :
      (fun lambda : ℝ =>
        ∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) =O[atTop]
          (fun lambda : ℝ =>
            ∏ _j ∈ range (r + 1), lambda⁻¹) := by
    apply IsBigO.finsetProd
    intro j hj
    simpa only [shiftedReciprocalNode, pow_one] using
      shiftedReciprocalNode_pow_isBigO_invPow_atTop j 1
  apply hprod.congr_right
  intro lambda
  simp

private theorem completeHomogeneous_shiftedReciprocal_isBigO_invPow_atTop
    (r n : ℕ) :
    (fun lambda : ℝ =>
      completeHomogeneousEvalOn (range (r + 1))
        (fun j ↦ (lambda + (j : ℝ))⁻¹) n) =O[atTop]
      (fun lambda : ℝ => lambda⁻¹ ^ n) := by
  apply completeHomogeneousEvalOn_isBigO_pow atTop
    (range (r + 1))
    (fun (j : ℕ) (lambda : ℝ) => (lambda + (j : ℝ))⁻¹)
    (fun lambda : ℝ => lambda⁻¹) n
  intro j hj
  simpa only [shiftedReciprocalNode, pow_one] using
    shiftedReciprocalNode_pow_isBigO_invPow_atTop j 1

/-- Every exact residual contribution has its expected inverse-phase order. -/
theorem fabiusPhaseLockedResidualTerm_isBigO
    (r n : ℕ) :
    (fun lambda : ℝ => fabiusPhaseLockedResidualTerm r n lambda)
      =O[atTop] (fun lambda : ℝ => lambda⁻¹ ^ (r + 1 + n)) := by
  have hprod := prod_shiftedReciprocal_isBigO_invPow_atTop r
  have hhom :=
    completeHomogeneous_shiftedReciprocal_isBigO_invPow_atTop r n
  have hcoeff :=
    fabiusSaddleLogCoefficient_isBigO_one_atTop (r + 1 + n)
  have h := (hprod.mul hhom).mul hcoeff
  have hscaled := h.const_mul_left ((-1 : ℝ) ^ r)
  apply hscaled.congr'
  · filter_upwards with lambda
    unfold fabiusPhaseLockedResidualTerm
    ring
  · filter_upwards with lambda
    rw [pow_add]
    ring

private theorem invPow_isBigO_invPow_of_le_atTop
    (q k : ℕ) (hk : q ≤ k) :
    (fun lambda : ℝ => lambda⁻¹ ^ k) =O[atTop]
      (fun lambda : ℝ => lambda⁻¹ ^ q) := by
  simpa only [pow_zero, one_mul] using
    pow_mul_invPow_isBigO_invPow_atTop 0 q k (by simpa using hk)

private theorem fabiusPhaseLockedResidualTerm_isBigO_of_le
    (r S n : ℕ) (hn : S ≤ n) :
    (fun lambda : ℝ => fabiusPhaseLockedResidualTerm r n lambda)
      =O[atTop] (fun lambda : ℝ => lambda⁻¹ ^ (r + 1 + S)) :=
  (fabiusPhaseLockedResidualTerm_isBigO r n).trans
    (invPow_isBigO_invPow_of_le_atTop (r + 1 + S) (r + 1 + n)
      (Nat.add_le_add_left hn (r + 1)))

private theorem fabiusPhaseLockedWeightedRemainder_isBigO
    (F : BoundedFabius) (hF : IsFabius F)
    (r N q : ℕ) (hN : r + q ≤ N) :
    (fun lambda : ℝ => fabiusPhaseLockedWeightedRemainder F r N lambda)
      =O[atTop] (fun lambda : ℝ => lambda⁻¹ ^ q) := by
  unfold fabiusPhaseLockedWeightedRemainder
  apply IsBigO.sum
  intro j hj
  have hjle : j ≤ r := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hmul :=
    (isBigO_refl
      (fun lambda : ℝ => shiftedReciprocalLagrangeWeight lambda r j)
      atTop).mul (fabiusPhaseLockedNodeRemainder_isBigO F hF j N)
  exact hmul.trans
    (shiftedReciprocalLagrangeWeight_mul_invPow_isBigO_atTop
      r j N q hjle hN)

private theorem fabiusPhaseLockedCoefficientMoment_eq_residualPartialSum
    (r N : ℕ) (hN : r + 1 ≤ N) (lambda : ℝ) :
    fabiusPhaseLockedCoefficientMoment r N lambda =
      fabiusPhaseLockedResidualPartialSum r (N - (r + 1)) lambda := by
  let T : ℕ := N - (r + 1)
  have hNT : r + 1 + T = N := by
    exact Nat.add_sub_of_le hN
  let M : ℕ → ℝ := fun k =>
    ∑ j ∈ range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j *
        (lambda + (j : ℝ))⁻¹ ^ k
  have hlow :
      (∑ k ∈ range (r + 1),
        fabiusSaddleLogCoefficient k lambda * M k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkle : k ≤ r := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    by_cases hkzero : k = 0
    · subst k
      simp only [fabiusSaddleLogCoefficient_zero, zero_mul]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
      have hmzero : M k = 0 := by
        simpa only [M] using
          sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_zero
            lambda r k hkpos hkle
      rw [hmzero, mul_zero]
  have hhigh (n : ℕ) :
      fabiusSaddleLogCoefficient (r + 1 + n) lambda * M (r + 1 + n) =
        fabiusPhaseLockedResidualTerm r n lambda := by
    rw [show M (r + 1 + n) =
        (-1 : ℝ) ^ r *
          (∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) *
          completeHomogeneousEvalOn (range (r + 1))
            (fun j ↦ (lambda + (j : ℝ))⁻¹) n by
      simpa only [M] using
        sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add
          lambda r n]
    unfold fabiusPhaseLockedResidualTerm
    ring
  unfold fabiusPhaseLockedCoefficientMoment
  rw [← hNT, Finset.sum_range_add, hlow, zero_add]
  unfold fabiusPhaseLockedResidualPartialSum T
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro n hn
  exact hhigh n

private theorem residualPartialSum_sub_isBigO
    (r S : ℕ) :
    (fun lambda : ℝ =>
      fabiusPhaseLockedResidualPartialSum r (r + S) lambda -
        fabiusPhaseLockedResidualPartialSum r S lambda) =O[atTop]
      (fun lambda : ℝ => lambda⁻¹ ^ (r + 1 + S)) := by
  have htail :
      (fun lambda : ℝ =>
        ∑ n ∈ Ico S (r + S),
          fabiusPhaseLockedResidualTerm r n lambda) =O[atTop]
        (fun lambda : ℝ => lambda⁻¹ ^ (r + 1 + S)) := by
    apply IsBigO.sum
    intro n hn
    exact fabiusPhaseLockedResidualTerm_isBigO_of_le r S n
      (Finset.mem_Ico.mp hn).1
  apply htail.congr_left
  intro lambda
  unfold fabiusPhaseLockedResidualPartialSum
  rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_left S r)]

/-! ## Phase-extraction theorem -/

/-- **Finite-order phase-locked extraction of the periodic endpoint term.**
After subtracting the first `S` exact residual moments, the reciprocal-grid
estimator has error `O(lambda⁻¹ ^ (r + 1 + S))` at positive infinity.

This is a genuine Poincaré statement for every fixed extrapolation order
`r` and residual depth `S`; it does not assert uniformity while either index
grows with `lambda`. -/
theorem fabiusPhaseLockedPeriodicEstimator_sub_residual_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (r S : ℕ) :
    (fun lambda : ℝ =>
      fabiusPhaseLockedPeriodicEstimator F r lambda -
        negativeLaplacePsi lambda -
        fabiusPhaseLockedResidualPartialSum r S lambda) =O[atTop]
      (fun lambda : ℝ => lambda⁻¹ ^ (r + 1 + S)) := by
  let N : ℕ := 2 * r + S + 1
  have hNlow : r + 1 ≤ N := by
    dsimp [N]
    omega
  have hNsub : N - (r + 1) = r + S := by
    dsimp [N]
    omega
  have hrem :
      (fun lambda : ℝ => fabiusPhaseLockedWeightedRemainder F r N lambda)
        =O[atTop] (fun lambda : ℝ => lambda⁻¹ ^ (r + 1 + S)) := by
    apply fabiusPhaseLockedWeightedRemainder_isBigO F hF
    dsimp [N]
    omega
  have htail := residualPartialSum_sub_isBigO r S
  apply (hrem.add htail).congr_left
  intro lambda
  rw [fabiusPhaseLockedPeriodicEstimator_sub_periodic_eq F r N lambda,
    fabiusPhaseLockedCoefficientMoment_eq_residualPartialSum
      r N hNlow lambda,
    hNsub]
  ring

/-- Without subtracting residual terms, the estimator recovers the periodic
correction with error `O(lambda⁻¹ ^ (r + 1))`. -/
theorem fabiusPhaseLockedPeriodicEstimator_sub_periodic_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    (fun lambda : ℝ =>
      fabiusPhaseLockedPeriodicEstimator F r lambda -
        negativeLaplacePsi lambda) =O[atTop]
      (fun lambda : ℝ => lambda⁻¹ ^ (r + 1)) := by
  simpa only [fabiusPhaseLockedResidualPartialSum, Finset.sum_range_zero,
    sub_zero, Nat.add_zero] using
      fabiusPhaseLockedPeriodicEstimator_sub_residual_isBigO F hF r 0

/-- Subtracting the first omitted reciprocal moment improves the estimator
error by one full inverse power. -/
theorem fabiusPhaseLockedPeriodicEstimator_sub_firstOmitted_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    (fun lambda : ℝ =>
      fabiusPhaseLockedPeriodicEstimator F r lambda -
        negativeLaplacePsi lambda -
        (-1 : ℝ) ^ r *
          (∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) *
          fabiusSaddleLogCoefficient (r + 1) lambda) =O[atTop]
      (fun lambda : ℝ => lambda⁻¹ ^ (r + 2)) := by
  simpa only [fabiusPhaseLockedResidualPartialSum,
    Finset.sum_range_one, fabiusPhaseLockedResidualTerm,
    completeHomogeneousEvalOn, completeHomogeneousEval_zero, mul_one,
    Nat.add_zero, Nat.add_assoc, Nat.add_left_inj] using
      fabiusPhaseLockedPeriodicEstimator_sub_residual_isBigO F hF r 1

/-- Along an additive integer ray, the phase-locked estimator converges to
the value of the periodic endpoint correction at the fixed base phase.
There is no corresponding unrestricted real limit because
`negativeLaplacePsi lambda` is itself oscillatory. -/
theorem fabiusPhaseLockedPeriodicEstimator_tendsto_periodicAlong
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) (a : ℝ) :
    Tendsto
      (fun n : ℕ =>
        fabiusPhaseLockedPeriodicEstimator F r (a + (n : ℝ)))
      atTop (nhds (negativeLaplacePsi a)) := by
  have hparameter :
      Tendsto (fun n : ℕ => a + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop a tendsto_natCast_atTop_atTop
  have herror :=
    (fabiusPhaseLockedPeriodicEstimator_sub_periodic_isBigO F hF r).comp_tendsto
      hparameter
  have hrate :
      Tendsto (fun n : ℕ => (a + (n : ℝ))⁻¹ ^ (r + 1))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply,
      zero_pow (by omega : r + 1 ≠ 0)] using
      (tendsto_inv_atTop_zero.comp hparameter).pow (r + 1)
  have hzero := herror.trans_tendsto hrate
  have hzero' :
      Tendsto
        (fun n : ℕ =>
          fabiusPhaseLockedPeriodicEstimator F r (a + (n : ℝ)) -
            negativeLaplacePsi a)
        atTop (nhds 0) := by
    apply hzero.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [show negativeLaplacePsi (a + (n : ℝ)) = negativeLaplacePsi a by
      simpa only [Nat.cast_ofNat, mul_one] using
        (negativeLaplacePsi_periodic.nat_mul n a)]
  exact tendsto_sub_nhds_zero_iff.mp hzero'

end

end Fabius
