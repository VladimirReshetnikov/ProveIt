import FabiusFunction.LambertPhaseLockedRichardson
import FabiusFunction.FabiusFullAsymptoticExpansion
import FabiusFunction.FabiusWikipediaMain

/-!
# Pulling the Fabius expansion back to phase-locked Lambert nodes

For a fixed natural translate `j`, the phase-locked node

`(lambda + j) * 2 ^ (-(lambda + j))`

tends to zero through positive arguments as `lambda → ∞`.  Once the
parameter is on the strict lower branch, its exact Lambert phase is
`lambda + j`.  Periodicity therefore freezes both the negative-Laplace
correction and every saddle coefficient at the base phase `lambda`.

This file combines that exact phase locking with the full small-argument
Fabius expansion.  It deliberately treats one fixed node at a time; bounds
for growing Richardson weights belong to a later finite-extrapolation layer.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

open Finset

noncomputable section

/-! ## The phase-locked path to the small-argument filter -/

/-- For every fixed natural translate, the phase-locked Lambert node tends
to zero from the right as its base phase tends to infinity. -/
theorem tendsto_lambertPhaseLockedNode_smallArgument (j : ℕ) :
    Tendsto (fun lambda : ℝ => lambertPhaseLockedNode lambda j)
      atTop (nhdsWithin 0 (Ioi 0)) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hshift : Tendsto (fun lambda : ℝ => lambda + (j : ℝ))
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (j : ℝ) tendsto_id
  have hzero : Tendsto (fun lambda : ℝ => lambertPhaseLockedNode lambda j)
      atTop (nhds 0) := by
    have hdecay :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (1 : ℝ) (Real.log 2) hlogTwo
    apply (hdecay.comp hshift).congr'
    filter_upwards with lambda
    simp only [Function.comp_apply, Real.rpow_one]
    unfold lambertPhaseLockedNode
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  have hpositive :
      ∀ᶠ lambda : ℝ in atTop, 0 < lambertPhaseLockedNode lambda j := by
    filter_upwards [hshift.eventually_gt_atTop 0] with lambda hlambda
    unfold lambertPhaseLockedNode
    exact mul_pos hlambda (Real.rpow_pos_of_pos (by norm_num) _)
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hzero, hpositive⟩

/-! ## Exact lower-branch bridges -/

/-- At a phase-locked node on the strict lower branch, the sharp Lambert
main is exactly the compact Wikipedia main plus the negative-Laplace
correction frozen at the base phase. -/
theorem fabiusSharpLambertMain_phaseLockedNode_eq_WikipediaLambertMain_add
    {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda) (j : ℕ) :
    fabiusSharpLambertMain (lambertPhaseLockedNode lambda j) =
      fabiusWikipediaLambertMain (lambertPhaseLockedNode lambda j) +
        negativeLaplacePsi lambda := by
  have hnode := lambertPhaseLockedNode_mem_lowerBranch hlambda j
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall :
      Real.log 2 * lambertPhaseLockedNode lambda j < Real.exp (-1) := by
    calc
      Real.log 2 * lambertPhaseLockedNode lambda j =
          lambertPhaseLockedNode lambda j * Real.log 2 := by ring
      _ < Real.exp (-1) := (lt_div_iff₀ hlogTwo).mp hnode.2
  calc
    fabiusSharpLambertMain (lambertPhaseLockedNode lambda j) =
        fabiusCorrectedWikipediaMain (lambertPhaseLockedNode lambda j) :=
      (fabiusCorrectedWikipediaMain_eq_sharpLambertMain
        hnode.1 hsmall).symm
    _ = fabiusWikipediaLambertMain (lambertPhaseLockedNode lambda j) +
        negativeLaplacePsi
          (fabiusLambertPhase (lambertPhaseLockedNode lambda j)) :=
      fabiusCorrectedWikipediaMain_eq_WikipediaLambertMain_add _
    _ = fabiusWikipediaLambertMain (lambertPhaseLockedNode lambda j) +
        negativeLaplacePsi lambda := by
      rw [Fabius.Periodic.apply_fabiusLambertPhase_phaseLockedNode
        negativeLaplacePsi_periodic hlambda j]

/-- The exact Wikipedia/sharp-main bridge holds eventually along every fixed
phase-locked path. -/
theorem eventually_fabiusSharpLambertMain_phaseLockedNode_eq_Wikipedia_add
    (j : ℕ) :
    ∀ᶠ lambda : ℝ in atTop,
      fabiusSharpLambertMain (lambertPhaseLockedNode lambda j) =
        fabiusWikipediaLambertMain (lambertPhaseLockedNode lambda j) +
          negativeLaplacePsi lambda := by
  filter_upwards [eventually_gt_atTop ((Real.log 2)⁻¹)]
    with lambda hlambda
  exact
    fabiusSharpLambertMain_phaseLockedNode_eq_WikipediaLambertMain_add
      hlambda j

/-- At a phase-locked node, the finite saddle sum has shifted reciprocal
powers while every periodic coefficient is frozen at the base phase. -/
theorem fabiusSaddleLogPartialSum_phaseLockedNode
    (N : ℕ) {lambda : ℝ} (hlambda : (Real.log 2)⁻¹ < lambda)
    (j : ℕ) :
    fabiusSaddleLogPartialSum N
        (fabiusLambertPhase (lambertPhaseLockedNode lambda j)) =
      ∑ k ∈ range N,
        (lambda + (j : ℝ))⁻¹ ^ k * fabiusSaddleLogCoefficient k lambda := by
  rw [fabiusLambertPhase_phaseLockedNode hlambda j]
  unfold fabiusSaddleLogPartialSum
  apply Finset.sum_congr rfl
  intro k _hk
  rw [show fabiusSaddleLogCoefficient k (lambda + (j : ℝ)) =
      fabiusSaddleLogCoefficient k lambda by
    simpa only [Nat.cast_ofNat, mul_one] using
      (fabiusSaddleLogCoefficient_periodic k).nat_mul j lambda]

/-! ## Single-node pullbacks of the full expansion -/

/-- The arbitrary-order sharp Lambert remainder pulled back along one fixed
phase-locked node.  Exact phase inversion turns its scale into the literal
shifted reciprocal power `(lambda + j)⁻¹ ^ N`. -/
theorem log_fabius_phaseLockedNode_sub_sharpLambertExpansion_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (j N : ℕ) :
    (fun lambda : ℝ =>
      Real.log (fabiusReal F (lambertPhaseLockedNode lambda j)) -
        fabiusSharpLambertExpansion N (lambertPhaseLockedNode lambda j))
      =O[atTop] (fun lambda : ℝ => (lambda + (j : ℝ))⁻¹ ^ N) := by
  have hcomp :=
    (log_fabius_sub_sharpLambertExpansion_isBigO F hF N).comp_tendsto
      (tendsto_lambertPhaseLockedNode_smallArgument j)
  apply hcomp.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [eventually_gt_atTop ((Real.log 2)⁻¹)]
      with lambda hlambda
    simp only [Function.comp_apply]
    rw [fabiusLambertPhase_phaseLockedNode hlambda j]

/-- The full single-node pullback in reduced Wikipedia form.  The
negative-Laplace correction and every saddle coefficient are evaluated at
the common base phase, while the inverse powers retain the node shift. -/
theorem log_fabius_phaseLockedNode_sub_WikipediaLambertExpansion_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (j N : ℕ) :
    (fun lambda : ℝ =>
      Real.log (fabiusReal F (lambertPhaseLockedNode lambda j)) -
        fabiusWikipediaLambertMain (lambertPhaseLockedNode lambda j) -
        negativeLaplacePsi lambda -
        ∑ k ∈ range N,
          (lambda + (j : ℝ))⁻¹ ^ k *
            fabiusSaddleLogCoefficient k lambda)
      =O[atTop] (fun lambda : ℝ => (lambda + (j : ℝ))⁻¹ ^ N) := by
  apply (log_fabius_phaseLockedNode_sub_sharpLambertExpansion_isBigO
    F hF j N).congr'
  · filter_upwards [eventually_gt_atTop ((Real.log 2)⁻¹)]
      with lambda hlambda
    rw [fabiusSharpLambertExpansion,
      fabiusSharpLambertMain_phaseLockedNode_eq_WikipediaLambertMain_add
        hlambda j,
      fabiusSaddleLogPartialSum_phaseLockedNode N hlambda j]
    ring
  · exact Filter.EventuallyEq.rfl

end

end Fabius
