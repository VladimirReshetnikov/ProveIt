import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalCenteredProductRate
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialRateFromConstant
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialRecomposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# Transfer a stored exponent polynomial to the original Barnes value

A Taylor polynomial for the exponent increment is evaluated on its
certified small disk. The exponential stability and finite
recomposition estimates then pass through the exact kept polynomial
and central exponential to the original shifted evaluator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorRecomposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCenteredExponentialShift (incrementF incrementData increment_regular valueData)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (evaluate ofGaussian)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticDivision (canonicalCoefficients)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "I" => GaussianRadiusExponentialName.nameF incrementF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "P" => GaussianBarnesCanonicalCenteredProductRate.nameF
local notation "pd" => GaussianBarnesCanonicalCenteredProductRate.data

def capGain (K : PTm n) : PTm n :=
  GaussianRadiusExponentialLipschitzRate.factor (GaussianNamedExponentialRateFromConstant.cap one K)

def error (A D m L H B K : PTm n) : PTm n :=
  leadingNumerator (capGain K*A) D
    (GaussianRationalPolynomialExponentialRecomposition.numerator m L (pw (num 3) L) H)
    (GaussianRationalPolynomialExponentialRecomposition.denominator m B)

def denominator (D m B : PTm n) : PTm n :=
  leadingDenominator D (GaussianRationalPolynomialExponentialRecomposition.denominator m B)

private theorem argument_bound (C N m w H B L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialRecomposition.input C N m w H B L) :
    Γ ⊢[PRAAx] bounded (evaluate C w) one one := by
  let hb := h.andE₂.andE₂.andE₂.andE₁
  let hH := h.andE₂.andE₂.andE₂.andE₂.andE₁
  let small := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  let mass := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  let hw := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have raw := GaussianRationalPolynomialExponentialRecomposition.evaluation_bound C N w H B L
    h.andE₁ h.andE₂.andE₁ hb hH mass hw
  have enlarge : Γ ⊢[PRAAx] le (L*H) (two*(L*H)) :=
    le_of_eq_add (d := L*H) (by ipra_ring)
  have fit : Γ ⊢[PRAAx] le ((L*H)*one) (one*B) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_trans enlarge small)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hb (le_refl one) fit raw

theorem exponential_rate (z h R B H C N m L A D K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hs : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialRecomposition.input C N m (ofGaussian h B) H B L)
    (hc : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B) (evaluate C (ofGaussian h B)) A D) :
    Γ ⊢[PRAAx] independentRate I constantF (valueData z h R B)
      (GaussianRationalPolynomialExponentialRecomposition.value C N m (ofGaussian h B))
      (error A D m L H B K) (denominator D m B) := by
  let w := ofGaussian h B
  let q := evaluate C w
  let f := GaussianRationalPolynomialExponentialRecomposition.nameF
  let u := GaussianRationalPolynomialExponentialRecomposition.data C w
  let v := GaussianRationalPolynomialExponentialRecomposition.value C N m w
  let e := GaussianRationalPolynomialExponentialRecomposition.denominator m B
  have he : Γ ⊢[PRAAx] le one e :=
    GaussianFactorBudget.power_positive B (succ m) hs.andE₂.andE₂.andE₂.andE₁
  have first := GaussianNamedExponentialRateFromConstant.rate incrementF
    (incrementData z h R B) q one A D K (increment_regular z h R B hz hw)
    (argument_bound C N m w H B L hs) hd hk hr
  have next := GaussianRationalPolynomialExponentialRecomposition.uniform_rate C N m w H B L hs hc
  exact GaussianNamedRateComposition.compose I f constantF (valueData z h R B) u v
    (capGain K*A) D _ e hd he first next

theorem rate (z h R B H C N m L A D K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hs : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialRecomposition.input C N m (ofGaussian h B) H B L)
    (hc : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le A (K*D))
    (hr : Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B) (evaluate C (ofGaussian h B)) A D) :
    Γ ⊢[PRAAx] independentRate V (P constantF) (vd (add z h) R B)
      (pd constantF z h R B (GaussianRationalPolynomialExponentialRecomposition.value C N m (ofGaussian h B)))
      (GaussianBarnesCanonicalCenteredProductRate.gain z R B*error A D m L H B K) (denominator D m B) := by
  have hn : Γ ⊢[PRAAx] le one (denominator D m B) :=
    GaussianRationalHorner.positive_product _ _ hd
      (GaussianFactorBudget.power_positive B (succ m) hs.andE₂.andE₂.andE₂.andE₁)
  exact GaussianBarnesCanonicalCenteredProductRate.rate constantF z h R B _ _ _ hz hw (constant_regular _) hn
    (exponential_rate z h R B H C N m L A D K hz hw hs hc hd hk hr)

theorem actual_Barnes_Taylor_recomposition_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     let C := var 5
     let N := var 6
     let m := var 7
     let L := var 8
     let A := var 9
     let D := var 10
     let K := var 11
     let w := ofGaussian h B
     (source z R B ⋏ (source (add z h) R B ⋏
       (GaussianRationalPolynomialExponentialRecomposition.input C N m w H B L ⋏
         (canonicalCoefficients C ⋏ (le one D ⋏ (le A (K*D) ⋏
           independentRate incrementF constantF (incrementData z h R B) (evaluate C w) A D)))))) ⟶
       independentRate V (P constantF) (vd (add z h) R B)
         (pd constantF z h R B (GaussianRationalPolynomialExponentialRecomposition.value C N m w))
         (GaussianBarnesCanonicalCenteredProductRate.gain z R B*error A D m L H B K) (denominator D m B)) := by
  refine closeUniv 12 (.impI ?_)
  exact rate _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorRecomposition
