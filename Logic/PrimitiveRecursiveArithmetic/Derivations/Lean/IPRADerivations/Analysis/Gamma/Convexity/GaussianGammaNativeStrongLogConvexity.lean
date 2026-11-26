import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicWeightedQuadraticName
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartTimeOrder
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaStrongLogConvexityAlgebra
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementConvexity

/-!
# The sharp strong log-convexity margin for positive rational Gamma

Apply ordinary log-Gamma convexity after a unit shift. Its exact
logarithmic recurrence supplies the original harmonic logarithm.
Subtracting the common weighted logarithm leaves the positive quadratic
margin, with coefficient corresponding to `1/(B/b)^2` on the bounded
argument interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeStrongLogConvexity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogConvexity (center_positive center_denominator_positive)
open GaussianGammaEulerRationalLogOrder (add_order add_interleave order_refl)
open GaussianGammaNativeLogConvexity (weighted_convexity)
open GaussianGammaNativeLogConvexityCore (nativeCenterData nativeWeightedData)
open GaussianGammaStrongLogConvexityAlgebra (swap_first cancel_common scaled_harmonic_rescale weighted_recurrence)
open GaussianHarmonicWeightedQuadraticValue (gapCode)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_data_congr scale_cross scaled_regular)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular source_shift)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => productF H
local notation "G" => productF logGammaF
local notation "C" => constantF

def harmonicData (w a b : PTm n) : PTm n := productData H w (hd a b)
def harmonicCenter (a d b r s : PTm n) : PTm n :=
  harmonicData (weight r s) (barycenter a d r s) (weight r s*b)
def harmonicWeighted (a d b r s : PTm n) : PTm n := addData (harmonicData (succ r) a b) (harmonicData s d b)
def lowerData (a d b B r s : PTm n) : PTm n := addData (gapCode a d B r s) (nativeCenterData a d b r s)

private theorem harmonic_regular (w a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN L (harmonicData w a b) :=
  GaussianHarmonicWeightedQuadraticName.scale_regular w a b hs.andE₁ hs.andE₂

theorem harmonic_order (a d b B r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le d B) :
    Γ ⊢[PRAAx] realOrder (addF C (addF L L)) L
      (addData (gapCode a d B r s) (harmonicWeighted a d b r s)) (harmonicCenter a d b r s) := by
  let W := weight r s
  let D := W*b
  let c := gapCode a d B r s
  let xl := harmonicData (succ r) (W*a) D
  let yl := harmonicData s (W*d) D
  let x := harmonicData (succ r) a b
  let y := harmonicData s d b
  let z := harmonicCenter a d b r s
  have hW : Γ ⊢[PRAAx] le one W := zero_lt_succ _
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hW hb
  have hDArg := le_trans ha had
  have ca : Γ ⊢[PRAAx] source a b := .andI ha hb
  have cd : Γ ⊢[PRAAx] source d b := .andI hDArg hb
  have rx := harmonic_regular (succ r) a b ca
  have ry := harmonic_regular s d b cd
  have rxl := harmonic_regular (succ r) (W*a) D (.andI (positive_product _ _ hW ha) hD)
  have ryl := harmonic_regular s (W*d) D (.andI (positive_product _ _ hW hDArg) hD)
  have rz := harmonic_regular W (barycenter a d r s) D (.andI (center_positive a d r s ha) hD)
  have rc := constant_regular (Γ := Γ) c
  have eq₁ := add_cross L L L L xl x yl y rxl rx ryl ry
    (scaled_harmonic_rescale a b W (succ r) ca hW) (scaled_harmonic_rescale d b W s cd hW)
  have eq₂ := add_cross C C (addF L L) (addF L L) c c (addData xl yl) (addData x y) rc rc
    (add_fast _ _ _ _ rxl ryl) (add_fast _ _ _ _ rx ry) (cross_refl _ _ rc) eq₁
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ eq₂) (cross_refl L z rz)
    (GaussianHarmonicWeightedQuadraticName.logarithm_concavity a d B D r s ha had hB hD)

theorem shifted_order (a d b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd' : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder (addF L G) (addF (addF L L) (addF G G))
      (addData (harmonicCenter a d b r s) (nativeCenterData a d b r s))
      (addData (harmonicWeighted a d b r s) (nativeWeightedData a d b r s)) := by
  let W := weight r s
  let z := barycenter a d r s
  let B := W*b
  let z' := barycenter (a+b) (d+b) r s
  let x := logGammaData (a+b) b
  let y := logGammaData (d+b) b
  let zl := harmonicCenter a d b r s
  let zg := nativeCenterData a d b r s
  let xa := harmonicData (succ r) a b
  let xd := harmonicData s d b
  let ya := productData logGammaF (succ r) (logGammaData a b)
  let yd := productData logGammaF s (logGammaData d b)
  have hA : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hD : Γ ⊢[PRAAx] source d b := .andI hd' hb
  have hZ : Γ ⊢[PRAAx] source z B :=
    .andI (center_positive a d r s ha) (center_denominator_positive b r s hb)
  have hA' := source_shift a b hA
  have hD' := source_shift d b hD
  have hZ' : Γ ⊢[PRAAx] source z' B :=
    .andI (center_positive (a+b) (d+b) r s hA'.andE₁) hZ.andE₂
  have ez : Γ ⊢[PRAAx] z' ≐ z+B := by dsimp [z',z,B,W,barycenter,weight]; ipra_ring
  have original := log_gamma_regular z' B hZ'
  have shifted := log_gamma_regular (z+B) B (source_shift z B hZ)
  have zEq := GaussianGammaCompactCutoffAlignment.cross_data_congr logGammaF logGammaF
    (logGammaData z' B) (logGammaData z' B) (logGammaData z' B) (logGammaData (z+B) B)
    (.eqRefl _) (gamma_data_congr _ _ _ _ ez (.eqRefl _)) (cross_refl _ _ original)
  have cEq := scale_cross W W (logGammaData z' B) (logGammaData (z+B) B)
    (.eqRefl _) original shifted zEq
  have lhs := cross_trans _ _ _ _ _ _ cEq (weighted_recurrence z B W hZ)
  have ax := harmonic_regular (succ r) a b hA
  have dx := harmonic_regular s d b hD
  have ay := scaled_regular (succ r) (logGammaData a b) (log_gamma_regular a b hA)
  have dy := scaled_regular s (logGammaData d b) (log_gamma_regular d b hD)
  have ae := scaled_regular (succ r) x (log_gamma_regular (a+b) b hA')
  have de := scaled_regular s y (log_gamma_regular (d+b) b hD')
  have pair := add_cross G (addF L G) G (addF L G) (productData logGammaF (succ r) x) (addData xa ya)
    (productData logGammaF s y) (addData xd yd) ae (add_fast _ _ _ _ ax ay) de (add_fast _ _ _ _ dx dy)
    (weighted_recurrence a b (succ r) hA) (weighted_recurrence d b s hD)
  have rhs := cross_trans _ _ _ _ _ _ pair (add_interleave L G L G xa ya xd yd ax ay dx dy)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ lhs) rhs
    (weighted_convexity (a+b) (d+b) b r s hA'.andE₁ hD'.andE₁ hb)

theorem strong_convexity (a d b B r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le d B) :
    Γ ⊢[PRAAx] realOrder (addF C G) (addF G G) (lowerData a d b B r s) (nativeWeightedData a d b r s) := by
  let W := weight r s
  let t := barycenter a d r s
  let c := gapCode a d B r s
  let x := harmonicWeighted a d b r s
  let y := nativeCenterData a d b r s
  let z := nativeWeightedData a d b r s
  let lc := harmonicCenter a d b r s
  have ha' : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hd' : Γ ⊢[PRAAx] source d b := .andI (le_trans ha had) hb
  have ht : Γ ⊢[PRAAx] source t (W*b) :=
    .andI (center_positive a d r s ha) (center_denominator_positive b r s hb)
  have hx : Γ ⊢[PRAAx] pointCN (addF L L) x :=
    add_fast _ _ _ _ (harmonic_regular (succ r) a b ha') (harmonic_regular s d b hd')
  have hy : Γ ⊢[PRAAx] pointCN G y := scaled_regular W _ (log_gamma_regular t (W*b) ht)
  have hz : Γ ⊢[PRAAx] pointCN (addF G G) z :=
    add_fast _ _ _ _ (scaled_regular (succ r) _ (log_gamma_regular a b ha')) (scaled_regular s _ (log_gamma_regular d b hd'))
  have hc := constant_regular (Γ := Γ) c
  have lo := add_order (addF C (addF L L)) L G G (addData c x) lc y y
    (harmonic_order a d b B r s ha had hb hB) (order_refl _ _ hy)
  have hi := shifted_order a d b r s ha hd'.andE₁ hb
  have comb := GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ lo hi
  have rebracket := add_associative C (addF L L) G c x y hc hx hy
  have rotate := swap_first C (addF L L) G c x y hc hx hy
  have recast := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ rebracket rotate))
    (cross_refl _ _ (add_fast _ _ _ _ hx hz)) comb
  exact cancel_common (addF L L) (addF C G) (addF G G) x (addData c y) z hx
    (add_fast _ _ _ _ hc hy) hz recast

theorem actual_positive_rational_log_Gamma_strong_convexity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 0) ⋏ (le (var 0) (var 1) ⋏ (le one (var 2) ⋏ le (var 1) (var 3)))) ⟶
      realOrder (addF C G) (addF G G) (lowerData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (nativeWeightedData (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.impI (strong_convexity _ _ _ _ _ _ Prf.hyp0.andE₁
      Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeStrongLogConvexity
