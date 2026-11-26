import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalWeightedTaylorRecomposition
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProduct
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialWeightedProductTruncation

/-!
# Weighted Taylor product for the original Barnes name

Weight the actual centered head and stored exponent at radius one quarter.
The Taylor polynomial and scalar name are the original stored product
and its original multiplier. Fixed-radius truncation supplies the
product tail at the same order as the weighted exponent recomposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData head incrementF incrementData)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProduct
  (nameF data polynomial headPolynomial headDegree tailNumerator gather_constants scaled_rate)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (evaluate ofGaussian ofGaussian_canonical qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPolynomialDilation (weightedNorm)
open RationalArgmin (rationalLE)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

def error (z R B A L H m J D K : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProduct.error z R B A L (num 4*H) m J D K

theorem rate (z h R B H p N m L A J D K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalWeightedTaylorRecomposition.input p N m (ofGaussian h B) H B L)
    (ha : Γ ⊢[PRAAx] rationalLE (weightedNorm (headPolynomial z R B) (headDegree R) (radiusPoint one (num 4)))
      (fraction A one))
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le J (K*D))
    (hr : Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B) (evaluate p (ofGaussian h B)) J D) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (add z h) R B) (data z h R B p N m)
      (error z R B A L H m J D K) (GaussianBarnesCanonicalTaylorRecomposition.denominator D m B) := by
  let w := ofGaussian h B
  let v := GaussianRationalPolynomialExponentialRecomposition.value p N m w
  let x := baseData z R B
  let b := qmul (head z h R B) v
  let y := multiplyData E constantF x b
  let j := tailNumerator z R B A L (num 4*H) m
  let e := pw B (succ m)
  let d := GaussianBarnesCanonicalTaylorRecomposition.denominator D m B
  have hB := hs.andE₂.andE₂.andE₂.andE₁
  have he : Γ ⊢[PRAAx] le one e := GaussianFactorBudget.power_positive B (succ m) hB
  have hden : Γ ⊢[PRAAx] le one d := positive_product D e hd he
  have approx := GaussianBarnesCanonicalWeightedTaylorRecomposition.rate z h R B H p N m L J D K hz hw hs hd hk hr
  have pre := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hden approx
    (cross_refl _ _ (GaussianBarnesCanonicalValue.regular (add z h) R B hw))
    (cross_symm _ _ _ _ (gather_constants z h R B v hz))
  have hP := GaussianBarnesCanonicalCenteredHead.polynomial_length (Γ := Γ) z B (initial R)
  have fit : Γ ⊢[PRAAx] le (num 4*H) (one*B) :=
    le_congr (.eqRefl _) (one_mul B).eqSymm hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have rawTail := GaussianRationalPolynomialExponentialWeightedProductTruncation.fixed_radius_tail
    (headPolynomial z R B) p (headDegree R) N m w one (num 4) H B A L
    hP hs.andE₁ hs.andE₂.andE₂.andE₁ (le_refl one) (zero_lt_succ _) hB fit (ofGaussian_canonical h B hB)
    hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂ ha hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have tail : Γ ⊢[PRAAx] distanceBounded b (evaluate (polynomial z R B p N m) w)
      ((A*pw (num 3) L)*pw (num 4*H) (succ m)) e :=
    distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (congrAp2 powF (.eqRefl (succ m)) (one_mul B)) rawTail
  have final : Γ ⊢[PRAAx] independentRate nameF nameF y (data z h R B p N m) j e :=
    scaled_rate z R B b _ _ e hz he tail
  have adjust : Γ ⊢[PRAAx] le (j*d) ((D*j)*e) :=
    le_of_eq_add (d := zero) (by dsimp [d,GaussianBarnesCanonicalTaylorRecomposition.denominator,
      GaussianRationalPolynomialExponentialRecomposition.denominator,leadingDenominator]; ipra_ring)
  exact GaussianNamedRateComposition.same_denominator V nameF nameF (vd (add z h) R B) y
    (data z h R B p N m) _ d _ hden pre
    (GaussianNamedRateRadius.weaken _ _ _ _ j e (D*j) d he hden adjust final)

theorem actual_weighted_Barnes_Taylor_product_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     let p := var 5
     let N := var 6
     let m := var 7
     let L := var 8
     let A := var 9
     let J := var 10
     let D := var 11
     let K := var 12
     let w := ofGaussian h B
     (source z R B ⋏ (source (add z h) R B ⋏
       (GaussianBarnesCanonicalWeightedTaylorRecomposition.input p N m w H B L ⋏
         (rationalLE (weightedNorm (headPolynomial z R B) (headDegree R) (radiusPoint one (num 4))) (fraction A one) ⋏
         (le one D ⋏ (le J (K*D) ⋏
           independentRate incrementF constantF (incrementData z h R B) (evaluate p w) J D)))))) ⟶
       independentRate V nameF (vd (add z h) R B) (data z h R B p N m)
         (error z R B A L H m J D K) (GaussianBarnesCanonicalTaylorRecomposition.denominator D m B)) :=
  closeUniv 13 (.impI (rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorProduct
