import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrementAffine
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrementConvexity
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogShift

/-!
# Finite observations of the log-gamma chord slopes

Normalized addition, multiplication and subtraction contribute explicit
dyadic errors. The slope of each unit interval is the actual harmonic
logarithm by the original log-gamma recurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementObservations

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData multiplyModulus sum_distance)
open GaussianNameEquivalence (cross_to_diagonal diagonal_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (distanceBounded bounded qsub)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product)
open GaussianRationalSyntheticDivision (qadd_sub_cancel qmul_congr qsub_congr)
open GaussianStirlingGammaFractionalIncrementAffine (upper_increment lower_increment)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_data_congr scaled_regular weighted_upper weighted_lower pred_positive)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGlobalBounds (small_join)
open GaussianStirlingGlobalBoundsShiftArguments (deltaF deltaData slopeF slopeData shiftedNumerator shifted_positive)
open GaussianStirlingNames (logXF logXData)
open RationalValueBounds (upper upper_of_radius upper_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num pred monus)
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => productF logGammaF
local notation "gd" => productData logGammaF
local notation "gl" => fun a : PTm n => logGammaData a one

def scaleCost (t x : PTm n) : PTm n := multiplyModulus constantF logGammaF (naturalPoint t) x+one
def weightedCost (t r s x y z : PTm n) : PTm n :=
  scaleCost t x+two+(GaussianNameRingLaws.three+(scaleCost r y+scaleCost s z))
def slopeCost (i r b : PTm n) : PTm n := multiplyModulus constantF logXF (fraction r b) (logXData i one)+one
def upperCost (i r b : PTm n) : PTm n :=
  num 6+weightedCost b r (monus b r) (logGammaData (shiftedNumerator i r b) b)
    (gl (succ i)) (gl i)+(num 5+slopeCost i r b)
def lowerCost (i r b : PTm n) : PTm n :=
  (slopeCost (pred i) r b+num 5)+weightedCost (r+b) r b (gl i) (gl (pred i))
    (logGammaData (shiftedNumerator i r b) b)+num 6

theorem scalar_upper (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx] upper (fstT q) (fstT r) A B :=
  upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hB h)

theorem scale_observation (t x p : PTm n) (hx : Γ ⊢[PRAAx] pointCN logGammaF x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (gd t x)) (natScale t (ap2 logGammaF p x))
      (scaleCost t x) (unit p) :=
  distance_congr (.eqRefl _) ((qmul_congr (constant_at _ _) (.eqRefl _)).eqTrans
    (natScale_as_product _ _).eqSymm) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF logGammaF (naturalPoint t) x p
      (constant_regular _) hx)

theorem weighted_at (p t r s x y z : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN logGammaF x) (hy : Γ ⊢[PRAAx] pointCN logGammaF y)
    (hz : Γ ⊢[PRAAx] pointCN logGammaF z)
    (h : Γ ⊢[PRAAx] realOrder G (addF G G) (gd t x) (addData (gd r y) (gd s z))) :
    Γ ⊢[PRAAx] upper (fstT (natScale t (ap2 logGammaF p x)))
      (fstT (qadd (natScale r (ap2 logGammaF p y)) (natScale s (ap2 logGammaF p z))))
      (weightedCost t r s x y z) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have first := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (scale_observation t x p hx))
  have middle := upper_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp)
    (real_order_at G (addF G G) (gd t x) (addData (gd r y) (gd s z)) p p h)
    (le_of_eq_add (d := zero) (by ipra_ring))
  have addError := GaussianNameRingLaws.add_sample_error G G (gd r y) (gd s z) p
    (scaled_regular r y hy) (scaled_regular s z hz)
  have sumError := sum_distance _ _ _ _ _ _ _ hp (scale_observation r y p hy) (scale_observation s z p hz)
  have last := scalar_upper _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp addError sumError)
  exact small_join _ _ _ _ _ p (small_join _ _ _ _ _ p first middle) last

theorem fraction_contracts (r b u v A D : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hrb : Γ ⊢[PRAAx] le r b) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded u v A D) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction r b) u) (qmul (fraction r b) v) A D := by
  let c := fraction r b
  have cb : Γ ⊢[PRAAx] bounded c r b :=
    GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point r b hb).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded r b hb)
  have raw := GaussianRationalReciprocal.bounded_product c (qsub u v) r b A D hb hD cb h
  have dist : Γ ⊢[PRAAx] distanceBounded (qmul c u) (qmul c v) (r*A) (b*D) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference c u v).eqSymm
      (.eqRefl _) (.eqRefl _) raw
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hb hD) hD _ dist
  exact le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono hrb (le_refl (A*D)))

theorem slope_raw_error (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] distanceBounded (ap2 slopeF p (slopeData i r b))
      (qmul (fraction r b) (ap2 logXF p (logXData i one))) (slopeCost i r b) (unit p) :=
  distance_congr (.eqRefl _) (qmul_congr (constant_at _ _) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF logXF (fraction r b) (logXData i one) p
      (constant_regular _) (GaussianHarmonicLogarithmName.name_regular i one (.andI hi (le_refl one))))

theorem unit_gamma_increment_at (i p : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 logGammaF p (gl (succ i))) (ap2 logGammaF p (gl i)))
      (ap2 logXF p (logXData i one)) (num 5) (unit p) := by
  let g := ap2 logGammaF p (gl i)
  let l := ap2 logXF p (logXData i one)
  have hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source i one := .andI hi (le_refl one)
  have hp := unit_positive (Γ := Γ) p
  have law := GaussianStirlingGammaLogShift.log_gamma_increment i one hs
  have diag := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ law)
  have named := GaussianNameRingLaws.add_sample_error logXF logGammaF (logXData i one) (gl i) p
    (GaussianHarmonicLogarithmName.name_regular i one hs) (log_gamma_regular i one hs)
  have sumError := distance_triangle_same _ _ _ _ _ _ hp diag named
  have same := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) g (unit p) hp
  have diff := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp sumError same
  have e1 := qsub_congr (congrAp2 logGammaF (.eqRefl p)
    (gamma_data_congr (Γ := Γ) (i+one) one (succ i) one (succ_eq_add_one i).eqSymm (.eqRefl _))) (.eqRefl g)
  have e2 := (qsub_congr (GaussianRationalLinearProduct.qadd_commutative (Γ := Γ) l g) (.eqRefl _)).eqTrans
    (qadd_sub_cancel g l (GaussianHarmonicLogarithmName.sample_real p i one).andE₁)
  exact distance_congr e1 e2 (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) diff

theorem upper_observation (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 deltaF p (deltaData i r b))) (fstT (ap2 slopeF p (slopeData i r b)))
      (upperCost i r b) (unit p) := by
  let j := shiftedNumerator i r b
  let x := logGammaData j b
  let y := gl (succ i)
  let z := gl i
  let s := monus b r
  have hp := unit_positive (Γ := Γ) p
  have hx := log_gamma_regular j b (.andI (shifted_positive i r b hi hb) hb)
  have hy : Γ ⊢[PRAAx] pointCN logGammaF y := log_gamma_regular (succ i) one (.andI (zero_lt_succ _) (le_refl _))
  have hz := log_gamma_regular i one (.andI hi (le_refl _))
  have raw := weighted_at p b r s x y z hx hy hz (weighted_upper i r b hi hb hr hrb)
  have drop := upper_increment (ap2 logGammaF p x) (ap2 logGammaF p y) (ap2 logGammaF p z)
    b r s (weightedCost b r s x y z) (unit p) hb (eq_add_of_le hrb) raw
  have middle := upper_mono _ _ _ _ (weightedCost b r s x y z) (unit p) (positive_product _ _ hb hp) drop
    (by ipra_le (Groth.ι (Q.mk Γ (weightedCost b r s x y z))*Groth.ι (Q.mk Γ (unit p)))*sl hb)
  have left := scalar_upper _ _ _ _ hp (GaussianNamedDifference.sample_error logGammaF logGammaF x z p hx hz)
  have rightRaw := fraction_contracts r b _ _ _ _ hb hrb hp (unit_gamma_increment_at i p hi)
  have right := scalar_upper _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp rightRaw
    (distance_symmetric _ _ _ _ hp (slope_raw_error i r b p hi)))
  exact small_join _ _ _ _ _ p (small_join _ _ _ _ _ p left middle) right

theorem lower_observation (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le two i) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 slopeF p (slopeData (pred i) r b))) (fstT (ap2 deltaF p (deltaData i r b)))
      (lowerCost i r b) (unit p) := by
  let k := pred i
  let j := shiftedNumerator i r b
  let x := logGammaData j b
  let v := gl k
  let z := gl i
  have hp := unit_positive (Γ := Γ) p
  have ik := pred_positive i hi
  have ii := le_trans RationalAlgebra.two_positive hi
  have hx := log_gamma_regular j b (.andI (shifted_positive i r b ii hb) hb)
  have hv := log_gamma_regular k one (.andI ik (le_refl _))
  have hz := log_gamma_regular i one (.andI ii (le_refl _))
  have raw := weighted_at p (r+b) r b z v x hz hv hx (weighted_lower i r b hi hb hr)
  have drop := lower_increment (ap2 logGammaF p x) (ap2 logGammaF p v) (ap2 logGammaF p z)
    b r (weightedCost (r+b) r b z v x) (unit p) hb raw
  have middle := upper_mono _ _ _ _ (weightedCost (r+b) r b z v x) (unit p) (positive_product _ _ hb hp) drop
    (by ipra_le (Groth.ι (Q.mk Γ (weightedCost (r+b) r b z v x))*Groth.ι (Q.mk Γ (unit p)))*sl hb)
  have prev := unit_gamma_increment_at k p ik
  have e := (pos_of_one_le ii).eqSymm
  have change := qsub_congr (congrAp2 logGammaF (.eqRefl p) (gamma_data_congr (succ k) one i one e (.eqRefl _))) (.eqRefl (ap2 logGammaF p v))
  have prev' := distance_congr change (.eqRefl _) (.eqRefl _) (.eqRefl _) prev
  have leftRaw := fraction_contracts r b _ _ _ _ hb hrb hp (distance_symmetric _ _ _ _ hp prev')
  have left := scalar_upper _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp (slope_raw_error k r b p ik) leftRaw)
  have right := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp
    (GaussianNamedDifference.sample_error logGammaF logGammaF x z p hx hz))
  exact small_join _ _ _ _ _ p (small_join _ _ _ _ _ p left middle) right

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementObservations
