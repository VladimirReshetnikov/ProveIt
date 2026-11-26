import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsFinite
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsDensities
import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPanelRotation
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSubtractiveSum

/-!
# Exact summation of the all-order derivative densities

Every summand is read from the existing periodic panel readers. The
actual interior derivative fold is the difference of the finite
lower-order, higher-order, and Bernoulli-mean sums.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsFold

open_ipra
open GaussianStirlingAllOrderPanelPartsFinite
  (interior interior_le_mesh parameters weightAt weightBody weight_at densityBody density_at interiorDensity)
open GaussianStirlingAllOrderPanelPartsDensities
  (lowScalar highScalar previousDensity nextDensity meanDensity density_identity)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPanelTail (panelBody panelData panel_row_at)
open GaussianStirlingAllOrderPanelRotation (nextBody next_term rotate)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderReciprocalGridError (original_weight gridDen)
open GaussianStirlingAllOrderCenteredBernoulli (sample endpoint_samples_zero)
open GaussianStirlingAllOrderKernel (row rowWeight multiply_zero_right)
open GaussianStirlingAllOrderSubtractiveSum (body data)
open GaussianEuclideanDistanceName (fraction)
open RationalArithmetic (multiply negative add)
open RationalAlgebra (add_congr multiply_congr negative_congr multiply_commutative add_commutative negative_minus_multiply)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalReciprocalPowerTail (add_zero_right)
open RationalFiniteSum (term termwiseEq)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum

def weightInput (U B M : PTm n) : PTm n := parameters U B M
def prevInput (e : ℕ) (U B M : PTm n) : PTm n := panelData (num (e-1)) U B M zero
def nextInput (e : ℕ) (U B M : PTm n) : PTm n := panelData (num (e+1)) U B M zero

def mass (e : ℕ) (N U B M : PTm n) : PTm n := rsum (nextBody (weightBody e)) N (weightInput U B M)
def previous (m e : ℕ) (N U B M : PTm n) : PTm n := rsum (nextBody (panelBody (m-1))) N (prevInput e U B M)
def following (m e : ℕ) (N U B M : PTm n) : PTm n := rsum (nextBody (panelBody m)) N (nextInput e U B M)

private def meanBody (e : ℕ) : PTm 2 := scaledBody (nextBody (weightBody e))
private def lowerBody (m e : ℕ) : PTm 2 := body (meanBody e) (nextBody (panelBody (m-1)))
private def recurrenceBody (m e : ℕ) : PTm 2 := body (scaledBody (lowerBody m e)) (scaledBody (nextBody (panelBody m)))

private def meanInput (m : ℕ) (U B M : PTm n) : PTm n := pairT (signedMean m) (weightInput U B M)
private def lowerInput (m e : ℕ) (U B M : PTm n) : PTm n := data (meanInput m U B M) (prevInput e U B M)
private def recurrenceInput (m e : ℕ) (U B M : PTm n) : PTm n :=
  data (pairT (lowScalar m) (lowerInput m e U B M)) (pairT (highScalar e) (nextInput e U B M))

private theorem original_at (e : ℕ) (he : 0<e) (U B M r : PTm n) :
    Γ ⊢[PRAAx] rowWeight (num (e-1)) U B M zero r ≐ weightAt e U B M r :=
  (original_weight e he U B M zero r).eqTrans
    (RationalNonnegativePowers.fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) (by unfold gridDen; ipra_ring)))

theorem prev_at (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M r : PTm n) :
    Γ ⊢[PRAAx] term (panelBody (m-1)) r (prevInput e U B M) ≐ previousDensity m e U B M r := by
  have h : m-1+1=m := by omega
  have r₁ := panel_row_at (Γ := Γ) (m-1) (num (e-1)) U B M zero r
  have r₂ := original_at (Γ := Γ) e (by omega) U B M r
  refine r₁.eqTrans ?_
  simpa only [row,h,previousDensity,weightAt] using multiply_congr (.eqRefl (sample m r M)) r₂

theorem next_at (m e : ℕ) (U B M r : PTm n) :
    Γ ⊢[PRAAx] term (panelBody m) r (nextInput e U B M) ≐ nextDensity m e U B M r := by
  have h : e+2-1=e+1 := by omega
  have r₁ := panel_row_at (Γ := Γ) m (num (e+1)) U B M zero r
  have r₂ := original_at (Γ := Γ) (e+2) (by omega) U B M r
  refine r₁.eqTrans ?_
  simpa only [row,h,nextDensity,weightAt] using multiply_congr (.eqRefl (sample (m+1) r M)) r₂

private theorem target_at (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M i : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] term (densityBody m e) i (parameters U B M) ≐ term (recurrenceBody m e) i (recurrenceInput m e U B M) := by
  let r := succ i
  have a : Γ ⊢[PRAAx] term (meanBody e) i (meanInput m U B M) ≐ meanDensity m e U B M r := by
    refine (scaled_term _ _ _ _).eqTrans ?_
    rw [next_term]
    exact multiply_congr (.eqRefl _) (weight_at e U B M r)
  have b : Γ ⊢[PRAAx] term (nextBody (panelBody (m-1))) i (prevInput e U B M) ≐ previousDensity m e U B M r := by
    rw [next_term]
    exact prev_at m e hm he U B M r
  have c : Γ ⊢[PRAAx] term (nextBody (panelBody m)) i (nextInput e U B M) ≐ nextDensity m e U B M r := by
    rw [next_term]
    exact next_at m e U B M r
  have d : Γ ⊢[PRAAx] term (lowerBody m e) i (lowerInput m e U B M) ≐
      sub (meanDensity m e U B M r) (previousDensity m e U B M r) :=
    (GaussianStirlingAllOrderSubtractiveSum.term_at _ _ _ _ _).eqTrans (add_congr a (negative_congr b))
  have e' : Γ ⊢[PRAAx] term (recurrenceBody m e) i (recurrenceInput m e U B M) ≐
      sub (multiply (lowScalar m) (sub (meanDensity m e U B M r) (previousDensity m e U B M r)))
        (multiply (highScalar e) (nextDensity m e U B M r)) :=
    (GaussianStirlingAllOrderSubtractiveSum.term_at _ _ _ _ _).eqTrans
      (add_congr ((scaled_term _ _ _ _).eqTrans (multiply_congr (.eqRefl _) d))
        (negative_congr ((scaled_term _ _ _ _).eqTrans (multiply_congr (.eqRefl _) c))))
  exact (density_at m e U B M i).eqTrans ((density_identity m e U B M r hU hM).eqTrans e'.eqSymm)

theorem fold_identity (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] interiorDensity m e U B M ≐
      sub (multiply (lowScalar m) (sub (multiply (signedMean m) (mass e (interior M) U B M))
        (previous m e (interior M) U B M))) (multiply (highScalar e) (following m e (interior M) U B M)) := by
  let N := interior M
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let a := Syn.shift U
  let b := Syn.shift B
  let c := Syn.shift M
  have t : Γ ⊢[PRAAx] termwiseEq (densityBody m e) (recurrenceBody m e) N (parameters U B M) (recurrenceInput m e U B M) := by
    refine .allI (.impI ?_)
    have hu : Δ ⊢[PRAAx] le one a := by simpa [Δ,a,Syn.shift,Fm.shift] using hU.shift.wk
    have hc : Δ ⊢[PRAAx] le one c := by simpa [Δ,c,Syn.shift,Fm.shift] using hM.shift.wk
    have q := target_at m e hm he a b c (var 0) hu hc
    simpa [recurrenceInput,lowerInput,meanInput,weightInput,prevInput,nextInput,lowScalar,highScalar,GaussianStirlingAllOrderReciprocalWeightError.coefficient,
      signedMean,GaussianStirlingAllOrderPanelDerivative.meanNumerator,BernoulliBounds.zint,Syn.shift,N,Δ,a,b,c] using
      RationalArgmin.rationalEq_congr (.eqRefl _) q (.eqRefl _)
  have s := RationalFiniteSum.sum_ext _ _ _ _ _ t
  have ℓ : Γ ⊢[PRAAx] rsum (lowerBody m e) N (lowerInput m e U B M) ≐
      sub (multiply (signedMean m) (mass e N U B M)) (previous m e N U B M) :=
    (GaussianStirlingAllOrderSubtractiveSum.sum_at _ _ _ _ _).eqTrans
      (add_congr (sum_homogeneous _ _ _ _) (.eqRefl _))
  exact s.eqTrans ((GaussianStirlingAllOrderSubtractiveSum.sum_at _ _ _ _ _).eqTrans
    (add_congr ((sum_homogeneous _ _ _ _).eqTrans (multiply_congr (.eqRefl _) ℓ))
      (negative_congr (sum_homogeneous _ _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsFold
