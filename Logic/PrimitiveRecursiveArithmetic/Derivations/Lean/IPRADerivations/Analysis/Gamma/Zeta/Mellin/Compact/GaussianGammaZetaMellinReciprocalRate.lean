import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinIntegrand
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerExponentCompactBounds

/-!
# Compact time modulus of the actual Mellin reciprocal

On [1/H,T], transport the common exponential modulus to the original
observation programs. The named inverse multiplies it by H².
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinReciprocalRate

open_ipra
open GaussianCompactLogarithmBounds (domain)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaZetaMellinIntegrand
  (exponentialF exponentialData denominatorF denominatorData denominator_regular denominator_apart
    reciprocalF reciprocalData reciprocal_bound)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNameEquivalence (cross_refl)
open GaussianNameRingLaws (oneF one_fast)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lipschitz (H T : PTm n) : PTm n := H*H*GaussianRadiusExponentialLipschitzRate.factor T

ipra_subst lipschitz

private theorem common_exponential_input (a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF T (radiusPoint a b) := by
  let x := radiusPoint a b
  have bound : Γ ⊢[PRAAx] bounded x T one :=
    bounded_radius_mono _ _ _ _ _ hb (le_refl one)
      (le_congr ((mul_comm a one).eqTrans (one_mul a)).eqSymm (.eqRefl _) ht)
      (radius_bounded a b hb)
  refine .andI (constant_regular x) (.allI ?_)
  have bs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) (Syn.shift T) one := by
    simpa only [Fm.shift,Syn.shift,GaussianRationalMetric.subst_bounded,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using bound.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples] using
    GaussianRationalReciprocal.bound_congr
      (GaussianGammaCanonicalExponent.constant_at (var 0) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) bs

theorem exponential_rate (a b c d T A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (ht : Γ ⊢[PRAAx] le a (T*b)) (hu : Γ ⊢[PRAAx] le c (T*d))
    (hD : Γ ⊢[PRAAx] le one D)
    (time : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) :
    Γ ⊢[PRAAx] independentRate exponentialF exponentialF (exponentialData a b) (exponentialData c d)
      (GaussianRadiusExponentialLipschitzRate.factor T*A) D := by
  let x := radiusPoint a b
  let y := radiusPoint c d
  let X := GaussianRadiusExponentialName.data T x
  let Y := GaussianRadiusExponentialName.data T y
  let R := GaussianNameBounds.U constantF x
  let S := GaussianNameBounds.U constantF y
  have cx := common_exponential_input a b T hb ht
  have cy := common_exponential_input c d T hd hu
  have ox := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF x (constant_regular x)
  have oy := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF y (constant_regular y)
  have near := GaussianNamedAddRate.constant_rate x y A D hD
    (distance_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb)
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point c d hd) (.eqRefl _) (.eqRefl _) time)
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate constantF constantF T x y A D
    (.andI hD (.andI cx (.andI cy near)))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF R T x x
    ox cx (cross_refl constantF x cx.andE₁)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF S T y y
    oy cy (cross_refl constantF y cy.andE₁)
  exact GaussianNamedRateTransport.transport exponentialF exponentialF exponentialF exponentialF
    X Y (exponentialData a b) (exponentialData c d) _ D hD common left right

theorem reciprocal_samples (a b H T : PTm n) (h : Γ ⊢[PRAAx] domain a b H T) :
    Γ ⊢[PRAAx] sampleBound reciprocalF (reciprocalData a b) H := by
  refine .allI ?_
  let s (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] domain (s a) (s b) (s H) (s T) :=
    by simpa [Fm.shift,Syn.shift,s] using h.shift
  have bound : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 reciprocalF (var 0) (reciprocalData (s a) (s b))) (s H) one :=
    bounded_radius_mono _ _ _ _ _ hs.andE₁.andE₁ (le_refl one)
      (le_congr ((mul_comm (s b) one).eqTrans (one_mul (s b))).eqSymm (.eqRefl _) hs.andE₂.andE₁)
      (reciprocal_bound (var 0) (s a) (s b) hs.andE₁.andE₁ hs.andE₁.andE₂)
  simpa only [sampleBound,GaussianGammaZetaMellinIntegrand.subst_reciprocalData,Syn.shift,s] using bound

theorem reciprocal_rate (a b c d H T A D : PTm n)
    (ha : Γ ⊢[PRAAx] domain a b H T) (hc : Γ ⊢[PRAAx] domain c d H T) (hD : Γ ⊢[PRAAx] le one D)
    (time : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) :
    Γ ⊢[PRAAx] independentRate reciprocalF reciprocalF (reciprocalData a b) (reciprocalData c d)
      (lipschitz H T*A) D := by
  let x := denominatorData a b
  let y := denominatorData c d
  let u := reciprocalData a b
  let v := reciprocalData c d
  let F := denominatorF
  let I := reciprocalF
  let L := GaussianRadiusExponentialLipschitzRate.factor T
  have hx := denominator_regular (Γ := Γ) a b
  have hy := denominator_regular (Γ := Γ) c d
  have ax := denominator_apart a b ha.andE₁.andE₁ ha.andE₁.andE₂
  have ay := denominator_apart c d hc.andE₁.andE₁ hc.andE₁.andE₂
  have hu := GaussianNameReciprocal.name_fast F b x hx ax
  have hv := GaussianNameReciprocal.name_fast F d y hy ay
  have ex := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF (radiusPoint a b)
    (constant_regular _)
  have ey := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF (radiusPoint c d)
    (constant_regular _)
  have de : Γ ⊢[PRAAx] independentRate F F x y (L*A) D :=
    GaussianNamedDifferenceRate.same_right_rate exponentialF exponentialF oneF
      (exponentialData a b) (exponentialData c d) zero (L*A) D hD
      (GaussianRadiusExponentialName.name_regular _ _ _ ex) (GaussianRadiusExponentialName.name_regular _ _ _ ey)
      (one_fast zero)
      (exponential_rate a b c d T A D ha.andE₁.andE₂ hc.andE₁.andE₂ ha.andE₂.andE₂ hc.andE₂.andE₂ hD time)
  have small (a b : PTm n) (h : Γ ⊢[PRAAx] domain a b H T) :
      Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples I (reciprocalData a b) H one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,sampleBound,Syn.shift,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using reciprocal_samples a b H T h
  have bound : Γ ⊢[PRAAx] GaussianNamedInverseRate.input F F I I x y u v H one (L*A) D :=
    .andI (le_refl one) (.andI hD (.andI (.andI hx hy) (.andI (.andI hu hv)
      (.andI (.andI (small a b ha) (small c d hc))
        (.andI (.andI (GaussianNameReciprocal.product_one F b x hx ax)
          (GaussianNameReciprocal.product_one F d y hy ay)) de)))))
  exact GaussianNamedDifferenceRate.rate_parameters_congr I I u v _ _ _ _
    (by unfold lipschitz L; ipra_ring) (by ipra_ring)
    (GaussianNamedInverseRate.inverse_rate F F I I x y u v H one (L*A) D bound)

theorem actual_Mellin_reciprocal_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let a := var 0
     let b := var 1
     let c := var 2
     let d := var 3
     let H := var 4
     let T := var 5
     let A := var 6
     let D := var 7
     (domain a b H T ⋏ (domain c d H T ⋏ (le one D ⋏ distanceBounded (fraction a b) (fraction c d) A D))) ⟶
       independentRate reciprocalF reciprocalF (reciprocalData a b) (reciprocalData c d) (lipschitz H T*A) D) :=
  closeUniv 8 (.impI (reciprocal_rate _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinReciprocalRate
