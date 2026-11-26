import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorRecomposition
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialFixedRadius
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Recompose the original Barnes exponential with a weighted Taylor mass

The one-quarter radius scales the displacement and the coefficient mass
in opposite directions. The exponential and the stored Taylor value are
still evaluated at the original displacement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorRecomposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCenteredExponentialShift (incrementF incrementData increment_regular)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorRecomposition (capGain error denominator)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (canonical evaluate ofGaussian qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalArgmin (rationalLE)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "P" => GaussianBarnesCanonicalCenteredProductRate.nameF
local notation "pd" => GaussianBarnesCanonicalCenteredProductRate.data

def input (C N m w H B L : PTm n) : Fm PTm n :=
  (length C ≐ succ N) ⋏ ((entry C N ≐ qzero) ⋏ (le m (m*N) ⋏
    (le one B ⋏ (le (num 4*H) B ⋏ (le (two*(L*(num 4*H))) B ⋏
      (rationalLE (weightedNorm C N (radiusPoint one (num 4))) (fraction L one) ⋏ bounded w H B))))))

private theorem argument_bound (C N m w H B L : PTm n)
    (hs : Γ ⊢[PRAAx] input C N m w H B L) (hCan : Γ ⊢[PRAAx] canonical w) :
    Γ ⊢[PRAAx] bounded (evaluate C w) one one := by
  let t : PTm n := radiusPoint one (num 4)
  let u := GaussianRationalTravelScaling.ratio one (num 4) w
  have hB := hs.andE₂.andE₂.andE₂.andE₁
  have hHB := hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have hSmall := hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hMass := hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hw := hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have h4 : Γ ⊢[PRAAx] le one (num 4) := zero_lt_succ _
  have hu := GaussianRationalPolynomialExponentialFixedRadius.normalized_bound w one (num 4) H B (le_refl one) hB hw
  have raw := GaussianRationalPolynomialExponentialRecomposition.evaluation_bound (dilated C N t) N
    u (num 4*H) B L (GaussianRationalPolynomialDilation.dilated_length C N t)
    (GaussianRationalPolynomialExponentialDilation.source_constant C N t hs.andE₂.andE₁)
    hB hHB hMass (GaussianRationalReciprocal.bound_congr (.eqRefl u) (.eqRefl _) (one_mul B) hu)
  have fit : Γ ⊢[PRAAx] le ((L*(num 4*H))*one) (one*B) := by
    have enlarge : Γ ⊢[PRAAx] le (L*(num 4*H)) (two*(L*(num 4*H))) :=
      le_of_eq_add (d := L*(num 4*H)) (by ipra_ring)
    exact le_congr (by ipra_ring) (by ipra_ring) (le_trans enlarge hSmall)
  have unitBound := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hB (le_refl one) fit raw
  have roundtrip := GaussianRationalPolynomialExponentialFixedRadius.normalized_roundtrip w one (num 4)
    (le_refl one) h4 hCan
  have eval := (GaussianRationalPolynomialDilation.dilation_evaluation C N t u hs.andE₁).eqTrans
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl C) roundtrip)
  exact GaussianRationalReciprocal.bound_congr eval (.eqRefl _) (.eqRefl _) unitBound

theorem named_exponential_rate (f : PR 2) (x C N m h H B L A D K : PTm n)
    (hreg : Γ ⊢[PRAAx] pointCN f x)
    (hs : Γ ⊢[PRAAx] input C N m (ofGaussian h B) H B L)
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate f constantF x (evaluate C (ofGaussian h B)) A D) :
    Γ ⊢[PRAAx] independentRate (GaussianRadiusExponentialName.nameF f) constantF (exponentialInputData f x)
      (GaussianRationalPolynomialExponentialRecomposition.value C N m (ofGaussian h B))
      (error A D m L (num 4*H) B K) (denominator D m B) := by
  let w := ofGaussian h B
  let g := GaussianRationalPolynomialExponentialRecomposition.nameF
  let u := GaussianRationalPolynomialExponentialRecomposition.data C w
  let v := GaussianRationalPolynomialExponentialRecomposition.value C N m w
  let E := GaussianRationalPolynomialExponentialRecomposition.numerator m L (pw (num 3) L) (num 4*H)
  let e := GaussianRationalPolynomialExponentialRecomposition.denominator m B
  let e' := GaussianRationalPolynomialExponentialRecomposition.denominator m (one*B)
  have hB := hs.andE₂.andE₂.andE₂.andE₁
  have hCan := GaussianRationalHorner.ofGaussian_canonical h B hB
  have he : Γ ⊢[PRAAx] le one e := GaussianFactorBudget.power_positive B (succ m) hB
  have heq : Γ ⊢[PRAAx] e' ≐ e := congrAp2 powF (.eqRefl _) (one_mul B)
  have he' := le_congr (.eqRefl one) heq.eqSymm he
  have first := GaussianNamedExponentialRateFromConstant.rate f x (evaluate C w) one A D K hreg
    (argument_bound C N m w H B L hs hCan) hd hk hr
  have scaled := GaussianRationalPolynomialExponentialFixedRadius.fixed_radius_rate C N m w one (num 4) H B L
    hs.andE₁ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ (le_refl one) (zero_lt_succ _) hB
    (le_congr (.eqRefl _) (one_mul B).eqSymm hs.andE₂.andE₂.andE₂.andE₂.andE₁)
    (le_congr (.eqRefl _) (one_mul B).eqSymm hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁)
    hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ hCan hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have next := GaussianNamedRateRadius.weaken g constantF u v E e' E e he' he
    (le_congr (.eqRefl _) (congrMul (.eqRefl E) heq.eqSymm) (le_refl (E*e))) scaled
  exact GaussianNamedRateComposition.compose (GaussianRadiusExponentialName.nameF f) g constantF
    (exponentialInputData f x) u v
    (capGain K*A) D E e hd he first next

theorem rate (z h R B H C N m L A D K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hs : Γ ⊢[PRAAx] input C N m (ofGaussian h B) H B L)
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B) (evaluate C (ofGaussian h B)) A D) :
    Γ ⊢[PRAAx] independentRate V (P constantF) (vd (add z h) R B)
      (pd constantF z h R B (GaussianRationalPolynomialExponentialRecomposition.value C N m (ofGaussian h B)))
      (GaussianBarnesCanonicalCenteredProductRate.gain z R B*error A D m L (num 4*H) B K)
      (denominator D m B) := by
  have hn : Γ ⊢[PRAAx] le one (denominator D m B) :=
    GaussianRationalHorner.positive_product _ _ hd
      (GaussianFactorBudget.power_positive B (succ m) hs.andE₂.andE₂.andE₂.andE₁)
  exact GaussianBarnesCanonicalCenteredProductRate.rate constantF z h R B _ _ _ hz hw (constant_regular _) hn
    (named_exponential_rate incrementF (incrementData z h R B) C N m h H B L A D K
      (increment_regular z h R B hz hw) hs hd hk hr)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorRecomposition
