import IPRADerivations.Analysis.GaussianBinetFixedHorizonPole
import IPRADerivations.Analysis.GaussianBinetSineDampedPanels

/-!
# The original sine transform on an independently chosen horizon

Both shifted exponential panel integrals use the same freely chosen
horizon. Their divided half difference approaches the exact sine
resolvent using only the checked lower bound on the real cutoff exponent.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonSine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code scale oneCode)
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianBinetArctangentResolvent (pole polynomial)
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetSineDampedPanels (multiplier multiplier_bound)
open GaussianBinetSineDampedTransform (coefficient_lower coefficient_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical ofGaussian_represents positive_product qmul qmul_canonical
  qmul_represents represents_congr)
open GaussianRationalLowerBounds (name_lower)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_neg im_neg re_scale im_scale re_one im_one)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LV" => GaussianBinetExponentialIntegralGrid.value
local notation "sineMultiplier" => GaussianNamedSineFromExponential.multiplier

def error (p R U K T L : PTm n) : PTm n := K*uniformCost (R+U) T*unit L+K*num 10*unit p

def value (p X Y D sign A B R U T N : PTm n) : PTm n :=
  qmul (multiplier A B) (qsub (LV (p+N) (qnegative (pole true X Y D sign A B)) ((R+U)*T) T N)
    (LV (p+N) (qnegative (pole false X Y D sign A B)) ((R+U)*T) T N))

@[simp] theorem subst_error {m : ℕ} (σ : Fin n → PTm m) (p R U K T L : PTm n) :
    Syn.subst σ (error p R U K T L) = error (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ U)
      (Syn.subst σ K) (Syn.subst σ T) (Syn.subst σ L) := by simp [error,uniformCost,two]

private theorem turn : Γ ⊢[PRAAx] qmul imaginaryPoint sineMultiplier ≐ (fraction one two : PTm n) := by
  let z := (imaginaryCode : PTm n)
  let w := ComplexLogarithmRemainder.neg z
  let a := scale one (oneCode : PTm n)
  have h := le_refl (Γ := Γ) one
  have h₂ := le_succ_self (Γ := Γ) one
  have rep := qmul_represents imaginaryPoint sineMultiplier z w one two h h₂
    (ofGaussian_represents z one h) (ofGaussian_represents w two h₂)
  apply canonical_unique _ _ a two (qmul_canonical _ _) (ofGaussian_canonical _ _ h₂) h₂
    (hrv := ofGaussian_represents a two h₂)
  apply represents_congr (.eqRefl _) (hAB := one_mul two) (h := rep)
  apply equal_of_values <;> simp [z,w,a,imaginaryCode,re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,
    eval_re_code,eval_im_code,ZT.toZ_ofNat]

theorem reciprocal_value (X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (multiplier A B) (qsub (reciprocal (pole true X Y D sign A B)) (reciprocal (pole false X Y D sign A B))) ≐
      reciprocal (polynomial X Y D sign A B) := by
  let c := coefficient A B (polarity true)
  let k := reciprocal c
  let W := reciprocal (polynomial X Y D sign A B)
  let d := qsub (reciprocal (pole true X Y D sign A B)) (reciprocal (pole false X Y D sign A B))
  have h := GaussianBinetSineLaplaceResolvent.reciprocal_difference X Y D sign A B hz hB
  have h₁ : Γ ⊢[PRAAx] qmul (fraction one two) d ≐ qmul imaginaryPoint (qmul sineMultiplier d) :=
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr turn (.eqRefl _))).eqSymm
  have h₂ : Γ ⊢[PRAAx] qmul imaginaryPoint (qmul sineMultiplier d) ≐ qmul c W :=
    (qmul_congr (.eqRefl _) h).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (coefficient_product A B hB) (.eqRefl _)))
  have norm := GaussianNameReciprocal.lower_norm_positive c B hB (name_lower c A B hA hB (coefficient_lower A B hB))
  have hc : Γ ⊢[PRAAx] qmul k c ≐ GaussianRationalSyntheticDivision.qone :=
    (qmul_commutative _ _).eqTrans (reciprocal_identity c norm)
  exact (qmul_associative k (fraction one two) d).eqTrans ((qmul_congr (.eqRefl _) (h₁.eqTrans h₂)).eqTrans
    ((qmul_associative k c W).eqSymm.eqTrans ((qmul_congr hc (.eqRefl _)).eqTrans
      ((qmul_commutative _ _).eqTrans (qmul_one_right W (reciprocal_canonical _))))))

theorem finite_error (p X Y D sign A B R U K T L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hcut : Γ ⊢[PRAAx] le (L*D) (X*T))
    (hL : Γ ⊢[PRAAx] le L p) (hN : Γ ⊢[PRAAx] le ((R+U)*T) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (value p X Y D sign A B R U T N) (reciprocal (polynomial X Y D sign A B))
      (B*(error p R U K T L+error p R U K T L)) (unit p*unit L) := by
  let E := error p R U K T L
  let H := unit p*unit L
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive L)
  have plus := GaussianBinetFixedHorizonPole.pole_integral_error true p X Y D sign A B R U K T L N hz hB hU hm hcut hL hN hpN
  have minus := GaussianBinetFixedHorizonPole.pole_integral_error false p X Y D sign A B R U K T L N hz hB hU hm hcut hL hN hpN
  have rate := GaussianNamedDifference.difference_distance _ _ _ _ E E H hH plus minus
  exact distance_congr (.eqRefl _) (reciprocal_value X Y D sign A B hz.andE₁ hA hB) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance (multiplier A B) _ _ B (E+E) H hH (multiplier_bound A B hA hB) rate)

end LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonSine
