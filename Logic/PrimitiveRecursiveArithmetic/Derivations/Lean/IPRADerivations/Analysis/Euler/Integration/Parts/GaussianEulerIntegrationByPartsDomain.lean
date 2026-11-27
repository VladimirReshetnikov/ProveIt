import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Analysis.Euler.VerticalBounds.Quadrature.GaussianEulerVerticalNamedRadius
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaEulerShiftLimit
import IPRADerivations.Analysis.Euler.CompactExhaustion.Cutoffs.GaussianEulerLaterCutoffObservation
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport

/-!
# Common cutoff domain for the two original Euler integrands

The input and its unit translate share the radius `R+1` and the
original real-part margin. Only the first argument changes radius.
The checked radius overlap identifies that enlarged original integral
with the original Gamma observation on the supplied disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsDomain

open_ipra
open GaussianEulerIntegralGammaIdentification (source original_Euler_integral_is_Gamma improper_source original_gamma_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerImproperName (nameF data name_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_two_errors)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerCutoffCauchyComparison (observation)
open GaussianNamedSmallPerturbationTransport (productClock product_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev productF : PR 2 := multiplyF constantF nameF
abbrev gammaProductF : PR 2 := multiplyF constantF gammaF
def productData (z R B A : PTm n) : PTm n := multiplyData constantF nameF (ofGaussian z B) (data z R B A)
def gammaProductData (z R B A : PTm n) : PTm n := multiplyData constantF gammaF (ofGaussian z B) (gammaData z R B A)

ipra_subst productData

theorem common_sources (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    source z (R+one) B A ⋏ source (shifted z B) (R+one) B A := by
  have hr : Γ ⊢[PRAAx] le R (R+one) := le_add_right R one
  have enlarged := GaussianEulerVerticalNamedRadius.source_enlarge z R (R+one) B A h hr
  have low := GaussianEulerBetaProductValue.shifted_source z B A
    (.andI h.andE₁.andE₂.andE₁.andE₁ (.andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂))
  have disk := GaussianGammaEulerShiftLimit.shifted_bound z R B h.andE₁.andE₂.andE₁.andE₂
  exact .andI enlarged (.andI (.andI low.andE₂.andE₁ (.andI (.andI low.andE₁ disk) low.andE₂.andE₂)) enlarged.andE₂)

theorem original_input_bound (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (ofGaussian z B) R one := by
  have hB := h.andE₁.andE₂.andE₁.andE₁
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents z B hB)
  exact le_congr (by ipra_ring) (by ipra_ring) h.andE₁.andE₂.andE₁.andE₂

theorem original_product_overlap (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent gammaProductF productF (gammaProductData z R B A) (productData z (R+one) B A) := by
  let S := R+one
  let c := ofGaussian z B
  have left := (common_sources z R B A h).andE₁
  have old := GaussianGammaHalfPlaneInputContinuity.reciprocal_source z R B A h
  have new := GaussianGammaHalfPlaneInputContinuity.reciprocal_source z S B A left
  have radii := GaussianGammaRadiusOverlap.original_Gamma_overlap z R S B one A one A old new
  have e := cross_trans _ _ _ _ _ _ radii (cross_symm _ _ _ _ (original_Euler_integral_is_Gamma z S B A left))
  have cc := constant_regular (Γ := Γ) c
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF gammaF nameF c c _ _ cc cc
    (original_gamma_regular z R B A h) (name_regular z S B A (improper_source z S B A left))
    (cross_refl _ _ cc) e

theorem original_product_to_fixed_cutoff (t q k z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hk : Γ ⊢[PRAAx] le t k) (hq : Γ ⊢[PRAAx] le (succ t) q) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF t (productData z R B A))
      (qmul (ofGaussian z B) (observation q z R B k A)) (two*R) (unit t) := by
  let c := ofGaussian z B
  let x := data z R B A
  let s := productClock constantF nameF c x t
  have hs : Γ ⊢[PRAAx] le t s := le_add_right _ _
  have old := GaussianEulerLaterCutoffObservation.later_cutoff_observations s q t z R B A k (improper_source z R B A h) hk hq
  have bounded := distance_two_errors _ _ _ _ _ (unit_positive s) (unit_positive t)
    (unit_positive t) (GaussianExponentialReference.unit_monotone hs) (le_refl _) old
  have sample : Γ ⊢[PRAAx] ap2 productF t (productData z R B A) ≐ qmul c (ap2 nameF s x) :=
    (product_at constantF nameF c x t).eqTrans (qmul_congr (constant_at s c) (.eqRefl _))
  exact distance_congr sample.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance _ _ _ _ _ _ (unit_positive t) (original_input_bound z R B A h) bounded)

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsDomain
