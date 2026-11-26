import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaUnitReciprocalShift
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalUnitInverseExpansion

/-!
# The actual Gamma sample and its reciprocal residual near one

The shifted Gamma data are those used by the original Euler divided
difference at one. Their fixed disk and positive half-plane margin
give an integer norm bound independent of the step denominator. The
original product law bounds the residual of the two actual observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaUnitInverseSamples

open_ipra
open GaussianGammaUnitEulerDifference (minimumDenominator original_source denominator_positive)
open GaussianGammaUnitReciprocalShift (neighbor large)
open GaussianGammaReciprocalInverse
  (gammaF gammaData gamma_regular gamma_product lambda_positive lambdaNumerator lambdaDenominator actual_gamma_observation_bound)
open GaussianGammaCanonicalExponent (constant_at)
open GaussianRationalUnitInverseExpansion (productResidual)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone qsub_congr)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (raw_inverse_residual residualCost)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (oneCode normSq_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def baseData : PTm n := gammaData oneCode one one one
def neighborData (D : PTm n) : PTm n := gammaData (neighbor D) (one+one) (one*D) (two*one)
def reciprocalData (D : PTm n) : PTm n := GaussianGammaC7Name.data (neighbor D) (one+one) (one*D)
def shiftedSample (t D : PTm n) : PTm n := ap2 gammaF t (neighborData D)
def normBudget : PTm n := lambdaDenominator (one+one) (two*one)+two
def residualBudget (D : PTm n) : PTm n := residualCost GaussianGammaC7Name.nameF gammaF (reciprocalData D) (neighborData D)

theorem original_shifted_source (s D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (neighbor D) (one+one) (one*D) one (two*one) :=
  GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _
    (GaussianGammaEulerFirstDerivative.shifted_source s oneCode one one one oneCode D (original_source s D h))

theorem original_base_source : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (oneCode : PTm n) one one one one :=
  GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _
    (.andI GaussianEulerUnitNormalization.unit_lower_source (le_refl one))

theorem neighbor_regular (s D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D) : Γ ⊢[PRAAx]
    pointCN gammaF (neighborData D) :=
  gamma_regular _ _ _ _ _ (original_shifted_source s D h)

theorem actual_step_separated (D : PTm n) (h : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianNamedDifferenceQuotient.separated oneCode D :=
  .andI h (le_congr (.eqRefl _) normSq_one.eqSymm (le_refl one))

theorem original_shifted_norm (s t D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D) : Γ ⊢[PRAAx]
    bounded (shiftedSample t D) normBudget one := by
  let L : PTm n := lambdaDenominator (one+one) (two*one)
  let N : PTm n := lambdaNumerator (one+one) one
  let U := unit t
  have hs := original_shifted_source s D h
  have raw : Γ ⊢[PRAAx] bounded (shiftedSample t D) (L*U+two*N) (N*U) :=
    actual_gamma_observation_bound t _ _ _ _ _ hs
  have hN : Γ ⊢[PRAAx] le one N := (lambda_positive _ _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁).andE₁
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hN hU) (le_refl one)
    (by change Γ ⊢[PRAAx] le ((L*U+two*N)*one) ((L+two)*(N*U))
        ipra_le 𝔞 L*𝔞 U*sl hN+2*𝔞 N*sl hU) raw

theorem original_residual (s t D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D) : Γ ⊢[PRAAx]
    bounded (productResidual (shiftedSample t D) (large t D)) (residualBudget D) (unit t) := by
  have hs := original_shifted_source s D h
  have raw := raw_inverse_residual GaussianGammaC7Name.nameF gammaF (reciprocalData D) (neighborData D) t
    (GaussianGammaC7Name.name_regular _ _ _ hs.andE₁) (neighbor_regular s D h) (gamma_product _ _ _ _ _ hs)
  exact bound_congr (qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)) (.eqRefl _) (.eqRefl _) raw

theorem original_base_observation (t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 gammaF t baseData) qone two (unit t) := by
  have U := unit_positive (Γ := Γ) t
  have value := GaussianNameEquivalence.cross_at _ _ _ _ t t
    (GaussianEulerUnitNormalization.original_Gamma_one_from_integral (Γ := Γ) (n := n))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ U U) U
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) (constant_at t qone) (.eqRefl _) (.eqRefl _) value)

theorem actual_positive_step_Gamma_sample_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (minimumDenominator (var 0)) (var 2) ⟶
      (bounded (shiftedSample (var 1) (var 2)) normBudget one ⋏
        bounded (productResidual (shiftedSample (var 1) (var 2)) (large (var 1) (var 2)))
          (residualBudget (var 2)) (unit (var 1)))) :=
  closeUniv 3 (.impI (.andI (original_shifted_norm _ _ _ Prf.hyp0) (original_residual _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaUnitInverseSamples
