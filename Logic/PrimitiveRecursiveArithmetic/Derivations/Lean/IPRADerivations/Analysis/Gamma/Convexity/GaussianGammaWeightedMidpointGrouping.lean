import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementConvexity
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogConvexity

/-!
# Splitting one midpoint pair from a weighted Gamma chord

For positive weights, set aside one copy of each endpoint. The remaining
weighted grouping is certified by two applications of the actual rational
log-Gamma convexity theorem, with their barycenters rescaled to the
original encoded rational arguments.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaWeightedMidpointGrouping

open_ipra
open GaussianGammaEulerRationalHeadConvexity (barycenter weight)
open GaussianGammaNativeLogConvexity (weighted_convexity)
open GaussianGammaNativeLogConvexityCore (nativeCenterData)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_rescale_from scale_cross scaled_regular)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => productF logGammaF
local notation "gd" => productData logGammaF

def groupNumerator (a d r : PTm n) : PTm n := succ r*a+d
def groupWeight (r : PTm n) : PTm n := succ (succ r)
def groupData (a d b r : PTm n) : PTm n := logGammaData (groupNumerator a d r) (groupWeight r*b)
def midpointData (a d b : PTm n) : PTm n := logGammaData (a+d) (two*b)

theorem group_numerator_positive (a d r : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (groupNumerator a d r) :=
  le_trans (positive_product _ _ (zero_lt_succ _) ha) (le_add_right _ _)

theorem group_denominator_positive (b r : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (groupWeight r*b) :=
  positive_product _ _ (zero_lt_succ _) hb

theorem first_group (a d b r : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder G (addF G G)
      (gd (groupWeight r) (groupData a d b r))
      (addData (gd two (midpointData a d b)) (gd r (logGammaData a b))) := by
  let A := a+d
  let D := two*a
  let B := two*b
  let t := barycenter A D one r
  let w := weight one r
  let u := groupNumerator a d r
  let v := groupWeight r
  let X := midpointData a d b
  let Y := logGammaData D B
  let Z := logGammaData t (w*B)
  have hA := le_trans ha (le_add_right a d)
  have hD := positive_product _ _ RationalAlgebra.two_positive ha
  have hB := positive_product _ _ RationalAlgebra.two_positive hb
  have hT := GaussianGammaEulerRationalLogConvexity.center_positive A D one r hA
  have hW := GaussianGammaEulerRationalLogConvexity.center_denominator_positive B one r hB
  have hu := group_numerator_positive a d r ha
  have hv := group_denominator_positive b r hb
  have e : Γ ⊢[PRAAx] w ≐ v := by dsimp [w,v,groupWeight,weight]; ipra_ring
  have et : Γ ⊢[PRAAx] t ≐ two*u := by dsimp [t,u,A,D,barycenter,groupNumerator]; ipra_ring
  have ed : Γ ⊢[PRAAx] w*B ≐ two*(v*b) :=
    (congrMul e (.eqRefl B)).eqTrans (by dsimp [B]; ipra_ring)
  have eqZ := gamma_rescale_from t (w*B) u (v*b) two (.andI hu hv) RationalAlgebra.two_positive et ed
  have eqY := gamma_rescale_from D B a b two (.andI ha hb) RationalAlgebra.two_positive (.eqRefl _) (.eqRefl _)
  have rx := log_gamma_regular A B (.andI hA hB)
  have ry := log_gamma_regular D B (.andI hD hB)
  have rz := log_gamma_regular t (w*B) (.andI hT hW)
  have rg := log_gamma_regular u (v*b) (.andI hu hv)
  have ri := log_gamma_regular a b (.andI ha hb)
  have left := scale_cross w v Z (groupData a d b r) e rz rg eqZ
  have right := add_cross G G G G (gd two X) (gd two X) (gd r Y) (gd r (logGammaData a b))
    (scaled_regular two X rx) (scaled_regular two X rx) (scaled_regular r Y ry) (scaled_regular r _ ri)
    (cross_refl _ _ (scaled_regular two X rx)) (scale_cross _ _ _ _ (.eqRefl _) ry ri eqY)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right
    (weighted_convexity A D B one r hA hD hB)

theorem second_group (a d b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder G (addF G G)
      (nativeCenterData a d b r (succ s))
      (addData (gd (groupWeight r) (groupData a d b r)) (gd s (logGammaData d b))) := by
  let k := groupWeight r
  let A := groupNumerator a d r
  let D := k*d
  let B := k*b
  let w := weight (succ r) s
  let t := barycenter A D (succ r) s
  let W := weight r (succ s)
  let T := barycenter a d r (succ s)
  let X := groupData a d b r
  let Y := logGammaData D B
  let Z := logGammaData t (w*B)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hA := group_numerator_positive a d r ha
  have hD := positive_product _ _ hk hd
  have hB := group_denominator_positive b r hb
  have hT := GaussianGammaEulerRationalLogConvexity.center_positive A D (succ r) s hA
  have hW := GaussianGammaEulerRationalLogConvexity.center_denominator_positive B (succ r) s hB
  have ht := GaussianGammaEulerRationalLogConvexity.center_positive a d r (succ s) ha
  have hw := GaussianGammaEulerRationalLogConvexity.center_denominator_positive b r (succ s) hb
  have e : Γ ⊢[PRAAx] w ≐ W := by dsimp [w,W,weight]; ipra_ring
  have et : Γ ⊢[PRAAx] t ≐ k*T := by
    dsimp [t,T,A,D,k,barycenter,groupNumerator,groupWeight]
    ipra_ring
  have ed : Γ ⊢[PRAAx] w*B ≐ k*(W*b) :=
    (congrMul e (.eqRefl B)).eqTrans (by dsimp [B]; ipra_ring)
  have eqZ := gamma_rescale_from t (w*B) T (W*b) k (.andI ht hw) hk et ed
  have eqY := gamma_rescale_from D B d b k (.andI hd hb) hk (.eqRefl _) (.eqRefl _)
  have rx := log_gamma_regular A B (.andI hA hB)
  have ry := log_gamma_regular D B (.andI hD hB)
  have rz := log_gamma_regular t (w*B) (.andI hT hW)
  have rg := log_gamma_regular T (W*b) (.andI ht hw)
  have ri := log_gamma_regular d b (.andI hd hb)
  have left := scale_cross w W Z (logGammaData T (W*b)) e rz rg eqZ
  have right := add_cross G G G G (gd k X) (gd k X) (gd s Y) (gd s (logGammaData d b))
    (scaled_regular k X rx) (scaled_regular k X rx) (scaled_regular s Y ry) (scaled_regular s _ ri)
    (cross_refl _ _ (scaled_regular k X rx)) (scale_cross _ _ _ _ (.eqRefl _) ry ri eqY)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right
    (weighted_convexity A D B (succ r) s hA hD hB)

end LeanProofs.IPRA.Analysis.GaussianGammaWeightedMidpointGrouping
