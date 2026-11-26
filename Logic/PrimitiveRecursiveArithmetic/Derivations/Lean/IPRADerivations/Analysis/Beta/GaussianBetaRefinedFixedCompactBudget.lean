import IPRADerivations.Analysis.Beta.GaussianBetaRefinedFixedCompactComparison
import IPRADerivations.Analysis.Names.GaussianFastValueCut

/-!
# Explicit dyadic thresholds for the original refined beta middle

The fixed compact Euler observation q and every positive refinement H
are unchanged. The actual beta error is reduced using the original
interval width and explicit degree and evaluation-precision thresholds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaRefinedFixedCompactBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianBetaKernelExponential (coefficient)
open GaussianBetaRefinedFixedCompactComparison (referencePrecision refinedBeta compactObservation)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def degreeCost (k A R : PTm n) : PTm n :=
  top k A R*(majorant R (etaDen k A R) (top k A R)*coefficient (top k A R)*top k A R*top k A R)
def precisionCost (k A R : PTm n) : PTm n :=
  top k A R*(majorant R (etaDen k A R) (top k A R)+two)
def minimumDegree (t k A R : PTm n) : PTm n :=
  one+two*top k A R+num 4*degreeCost k A R*unit t
def minimumPrecision (t q k A R : PTm n) : PTm n :=
  referencePrecision q k A R+GaussianFastValueCut.exponent (num 4*precisionCost k A R) t

/-- Three quarter-budget estimates suffice for the literal common
native denominator; the unused fourth quarter is retained as slack. -/
theorem scalar_budget (C E T F G N P Q U : PTm n)
    (hWidth : Γ ⊢[PRAAx] le C (E*T))
    (hDegree : Γ ⊢[PRAAx] le (num 4*(T*F)*U) N)
    (hPrecision : Γ ⊢[PRAAx] le (num 4*(T*G)*U) P)
    (hRefinement : Γ ⊢[PRAAx] le (num 12*U) Q) : Γ ⊢[PRAAx]
    le ((C*(F*P+G*N)*Q+num 3*(E*(N*P)))*U) (E*(N*P)*Q) := by
  have fourfold : Γ ⊢[PRAAx]
      le (num 4*((C*(F*P+G*N)*Q+num 3*(E*(N*P)))*U)) (num 4*(E*(N*P)*Q)) := by
    ipra_le (𝔞 (num 4*(F*P+G*N)*Q*U))*sl hWidth+
      (𝔞 (E*P*Q))*sl hDegree+(𝔞 (E*N*Q))*sl hPrecision+
      (𝔞 (E*N*P))*sl hRefinement+𝔞 (E*N*P*Q)
  exact RationalValueBounds.positive_cancel (le_of_eq_add (d := num 3) (by ipra_ring)) fourfold

theorem refinement_budget (t q : PTm n) (h : Γ ⊢[PRAAx] le t q) : Γ ⊢[PRAAx]
    le (num 12*unit t) (unit (q+num 6)) := by
  have square : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  have fourth : Γ ⊢[PRAAx] pw two (two+two) ≐ num 16 :=
    (pw_add two two two).eqTrans ((congrMul square square).eqTrans (by ipra_ring))
  have eval : Γ ⊢[PRAAx] pw two (num 6) ≐ num 64 :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 6 ≐ (two+two)+two) (.eqRefl _)).eqTrans
      ((pw_add two (two+two) two).eqTrans ((congrMul fourth square).eqTrans (by ipra_ring)))
  have split : Γ ⊢[PRAAx] unit (t+num 6) ≐ unit t*num 64 :=
    (pw_add two t (num 6)).eqTrans (congrMul (.eqRefl _) eval)
  have first : Γ ⊢[PRAAx] le (num 12*unit t) (unit (t+num 6)) :=
    le_congr (.eqRefl _) split.eqSymm (le_of_eq_add (d := num 52*unit t) (by ipra_ring))
  exact le_trans first (GaussianExponentialReference.unit_monotone (add_le_add_right (num 6) h))

theorem degree_threshold (t k A R N : PTm n)
    (h : Γ ⊢[PRAAx] le (minimumDegree t k A R) N) : Γ ⊢[PRAAx]
    le one N ⋏ (le (two*top k A R) N ⋏ le (num 4*degreeCost k A R*unit t) N) := by
  have first : Γ ⊢[PRAAx] le one (minimumDegree t k A R) :=
    le_of_eq_add (d := two*top k A R+num 4*degreeCost k A R*unit t) (by unfold minimumDegree; ipra_ring)
  have second : Γ ⊢[PRAAx] le (two*top k A R) (minimumDegree t k A R) :=
    le_of_eq_add (d := one+num 4*degreeCost k A R*unit t) (by unfold minimumDegree; ipra_ring)
  have third : Γ ⊢[PRAAx] le (num 4*degreeCost k A R*unit t) (minimumDegree t k A R) :=
    le_of_eq_add (d := one+two*top k A R) (by unfold minimumDegree; ipra_ring)
  exact .andI (le_trans first h) (.andI (le_trans second h) (le_trans third h))

theorem precision_threshold (t q k A R p : PTm n)
    (h : Γ ⊢[PRAAx] le (minimumPrecision t q k A R) p) : Γ ⊢[PRAAx]
    le (referencePrecision q k A R) p ⋏ le (num 4*precisionCost k A R*unit t) (unit p) := by
  have first : Γ ⊢[PRAAx] le (referencePrecision q k A R) (minimumPrecision t q k A R) :=
    le_add_right _ _
  have second : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (num 4*precisionCost k A R) t) (minimumPrecision t q k A R) :=
    le_of_eq_add (d := referencePrecision q k A R) (by unfold minimumPrecision; ipra_ring)
  exact .andI (le_trans first h) (le_trans (GaussianFastValueCut.query_budget _ _)
    (GaussianExponentialReference.unit_monotone (le_trans second h)))

/-- The SAME fixed q observation is within the requested dyadic radius
of every sufficiently evaluated beta degree and every positive mesh refinement. -/
theorem original_refined_middle_dyadic (p q t H z R B k A N : PTm n)
    (hSource : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hH : Γ ⊢[PRAAx] le one H) (htq : Γ ⊢[PRAAx] le t q)
    (hN : Γ ⊢[PRAAx] le (minimumDegree t k A R) N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t q k A R) p) : Γ ⊢[PRAAx]
    distanceBounded (refinedBeta p q H z R B k A N) (compactObservation q z R B k A) one (unit t) := by
  let E := etaDen k A R
  let C := width k A R
  let T := top k A R
  let F := majorant R E T*coefficient T*T*T
  let G := majorant R E T+two
  have deg := degree_threshold t k A R N hN
  have prec := precision_threshold t q k A R p hp
  have nativeWidth : Γ ⊢[PRAAx] le C (E*T) :=
    le_of_eq_add (d := one) (by exact (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A R).eqSymm.eqTrans (by ipra_ring))
  have raw := scalar_budget C E T F G N (unit p) (unit (q+num 6)) (unit t) nativeWidth
    deg.andE₂.andE₂ prec.andE₂ (refinement_budget t q htq)
  have compare : Γ ⊢[PRAAx]
      le (GaussianBetaRefinedFixedCompactComparison.numerator p q R k A N*unit t)
        (one*GaussianBetaRefinedFixedCompactComparison.denominator p q k A R N) := by
    simpa only [GaussianBetaRefinedFixedCompactComparison.numerator,
      GaussianBetaRefinedFixedCompactComparison.denominator,
      GaussianBetaRefinedFixedCompactComparison.betaNumerator,
      GaussianBetaRefinedFixedCompactComparison.betaDenominator,
      GaussianBetaKernelGridComparison.rowNumerator,E,C,T,F,G] using
      le_congr (.eqRefl _) (by ipra_ring) raw
  have old := GaussianBetaRefinedFixedCompactComparison.original_refined_beta_comparison p q H z R B k A N
    (.andI hSource (.andI hH (.andI prec.andE₁ (.andI deg.andE₁ deg.andE₂.andE₁))))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive k A R)
      (positive_product _ _ deg.andE₁ (unit_positive p))) (unit_positive (q+num 6)))
    (unit_positive t) compare old

theorem computed_middle_dyadic (q t H z R B k A : PTm n)
    (hSource : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hH : Γ ⊢[PRAAx] le one H) (htq : Γ ⊢[PRAAx] le t q) : Γ ⊢[PRAAx]
    distanceBounded
      (refinedBeta (minimumPrecision t q k A R) q H z R B k A (minimumDegree t k A R))
      (compactObservation q z R B k A) one (unit t) :=
  original_refined_middle_dyadic _ _ _ _ _ _ _ _ _ _ hSource hH htq (le_refl _) (le_refl _)

theorem original_arbitrarily_refined_middle_exact_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((GaussianGammaEulerCompactQuadrature.source (var 4) (var 5) (var 6) ⋏
      (le one (var 3) ⋏ (le (var 2) (var 1) ⋏
        (le (minimumDegree (var 2) (var 7) (var 8) (var 5)) (var 9) ⋏
          le (minimumPrecision (var 2) (var 1) (var 7) (var 8) (var 5)) (var 0))))) ⟶
      distanceBounded (refinedBeta (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (compactObservation (var 1) (var 4) (var 5) (var 6) (var 7) (var 8)) one (unit (var 2))) :=
  closeUniv 10 (.impI (original_refined_middle_dyadic _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

theorem original_computed_middle_exact_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaEulerCompactQuadrature.source (var 3) (var 4) (var 5) ⋏
      (le one (var 2) ⋏ le (var 1) (var 0))) ⟶
      distanceBounded
        (refinedBeta (minimumPrecision (var 1) (var 0) (var 6) (var 7) (var 4)) (var 0) (var 2)
          (var 3) (var 4) (var 5) (var 6) (var 7) (minimumDegree (var 1) (var 6) (var 7) (var 4)))
        (compactObservation (var 0) (var 3) (var 4) (var 5) (var 6) (var 7)) one (unit (var 1))) :=
  closeUniv 8 (.impI (computed_middle_dyadic _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaRefinedFixedCompactBudget
