import IPRADerivations.Analysis.Euler.HarmonicLogarithms.QuadraticBounds.GaussianHarmonicWeightedQuadraticValue
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.OrderedNames.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementObservations

/-!
# Strong concavity of the original rational harmonic logarithm

The same mesh appears in all three original observations. Normalizing
the named additions and scales contributes only dyadic errors, and
the exact rational gap survives removal of the common slack.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicWeightedQuadraticName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianHarmonicWeightedQuadratic (squareDen meshError)
open GaussianHarmonicWeightedQuadraticValue (gapCode point raw_upper comparison_denominator_positive)
open GaussianNameArithmetic (addF addData add_fast multiplyModulus sum_distance)
open GaussianNameRingLaws (add_sample_error multiply_sample_error)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product natScale_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGlobalBounds (small_join)
open RationalValueBounds (upper upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "G" => productF H
local notation "gd" => productData H
local notation "C" => constantF

def centerData (a d D r s : PTm n) : PTm n := gd (weight r s) (hd (barycenter a d r s) D)
def weightedData (a d B D r s : PTm n) : PTm n :=
  addData (gapCode a d B r s) (addData (gd (succ r) (hd (weight r s*a) D)) (gd s (hd (weight r s*d) D)))
def scaleCost (t x D : PTm n) : PTm n := multiplyModulus C H (naturalPoint t) (hd x D)+one
def observationCost (a d B D r s : PTm n) : PTm n :=
  ((GaussianNameRingLaws.three+(zero+(GaussianNameRingLaws.three+
    (scaleCost (succ r) (weight r s*a) D+scaleCost s (weight r s*d) D))))+meshError a d r s)+
    scaleCost (weight r s) (barycenter a d r s) D

ipra_subst centerData [weight, barycenter]
ipra_subst weightedData [weight]
ipra_subst scaleCost
ipra_subst observationCost [GaussianNameRingLaws.three, weight, barycenter]

theorem scale_regular (t x D : PTm n) (hx : Γ ⊢[PRAAx] le one x) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] pointCN G (gd t (hd x D)) :=
  GaussianNameArithmetic.multiply_fast C H _ _ (constant_regular _)
    (GaussianHarmonicLogarithmName.name_regular x D (.andI hx hD))

theorem scale_at (t x D p : PTm n) (hx : Γ ⊢[PRAAx] le one x) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (gd t (hd x D)))
      (natScale t (point x D (GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock p)))) (scaleCost t x D) (unit p) := by
  have e : Γ ⊢[PRAAx] qmul (ap2 C p (naturalPoint t)) (ap2 H p (hd x D)) ≐
      natScale t (point x D (GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock p))) :=
    (qmul_congr (constant_at p (naturalPoint t)) (Prf.eqRefl (ap2 H p (hd x D)))).eqTrans
    ((natScale_as_product t (ap2 H p (hd x D))).eqSymm.eqTrans
      (natScale_congr (.eqRefl _) (GaussianHarmonicLogarithmName.sample_at p x D)))
  exact distance_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _)
    (multiply_sample_error C H (naturalPoint t) (hd x D) p (constant_regular _)
      (GaussianHarmonicLogarithmName.name_regular x D (.andI hx hD)))

theorem observation (a d B D r s p : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hdB : Γ ⊢[PRAAx] le d B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (addF C (addF G G)) p (weightedData a d B D r s)))
      (fstT (ap2 G p (centerData a d D r s))) (observationCost a d B D r s) (unit p) := by
  let Q := GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock p)
  let P := squareDen B r s
  let W := weight r s
  let R := succ r
  let X := W*a
  let Y := W*d
  let Z := barycenter a d r s
  let c := gapCode a d B r s
  let A := gd R (hd X D)
  let B' := gd s (hd Y D)
  have hp := unit_positive (Γ := Γ) p
  have hP := comparison_denominator_positive B r s (le_trans ha (le_trans had hdB))
  have hQ := GammaEulerConstantName.mesh_positive (Γ := Γ) (GaussianHarmonicLogarithmName.clock p)
  have hW : Γ ⊢[PRAAx] le one W := zero_lt_succ _
  have hX := positive_product _ _ hW ha
  have hY := positive_product _ _ hW (le_trans ha had)
  have hZ : Γ ⊢[PRAAx] le one (barycenter a d r s) :=
    le_trans (positive_product _ _ (zero_lt_succ r) ha) (le_add_right _ _)
  have hT := scale_regular R X D hX hD
  have hU := scale_regular s Y D hY hD
  have vs := sum_distance _ _ _ _ _ _ _ hp (scale_at R X D p hX hD) (scale_at s Y D p hY hD)
  have v := distance_triangle_same _ _ _ _ _ _ hp (add_sample_error G G A B' p hT hU) vs
  have exactConstant : Γ ⊢[PRAAx] distanceBounded (ap2 C p c) c zero (unit p) :=
    distance_congr (constant_at p c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero c (unit p) hp)
  have outer := add_sample_error C (addF G G) c (addData A B') p (constant_regular _)
    (add_fast _ _ _ _ hT hU)
  have left := scalar_upper _ _ _ _ hp
    (distance_triangle_same _ _ _ _ _ _ hp outer (sum_distance _ _ _ _ _ _ _ hp exactConstant v))
  have right := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (scale_at W Z D p hZ hD))
  have raw := raw_upper a d B D Q r s ha had hdB hQ
  have uq : Γ ⊢[PRAAx] le (unit p) Q := by
    have late := GaussianBalancedRadiusArithmetic.unit_monotone (Γ := Γ) p (GaussianHarmonicLogarithmName.clock p)
      (le_add_right p (num 9))
    have mesh : Γ ⊢[PRAAx] le (unit (GaussianHarmonicLogarithmName.clock p)) Q := by
      dsimp [Q,GammaEulerConstantName.mesh,GammaEulerConstantName.unit,unit]
      ipra_le 3*Groth.ι (IPRA.Q.mk Γ (pw two (GaussianHarmonicLogarithmName.clock p)))
    exact le_trans late mesh
  have budget : Γ ⊢[PRAAx] le (unit p) (P*Q) :=
    le_trans uq (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right Q hP))
  have middle := upper_mono _ _ _ _ (meshError a d r s) (unit p) (positive_product _ _ hP hQ) raw
    (le_mul_mono (le_refl (meshError a d r s)) budget)
  exact small_join _ _ _ _ _ p (small_join _ _ _ _ _ p left middle) right

theorem logarithm_concavity (a d B D r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hdB : Γ ⊢[PRAAx] le d B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] realOrder (addF C (addF G G)) G (weightedData a d B D r s) (centerData a d D r s) := by
  have hW : Γ ⊢[PRAAx] le one (weight r s) := zero_lt_succ _
  have hX := positive_product _ _ hW ha
  have hY := positive_product _ _ hW (le_trans ha had)
  have hZ : Γ ⊢[PRAAx] le one (barycenter a d r s) :=
    le_trans (positive_product _ _ (zero_lt_succ r) ha) (le_add_right _ _)
  apply GaussianNamedRealOrderEnvelope.order_from_envelope (addF C (addF G G)) G (weightedData a d B D r s) (centerData a d D r s) (observationCost a d B D r s)
    (add_fast _ _ _ _ (constant_regular _) (add_fast _ _ _ _ (scale_regular _ _ _ hX hD) (scale_regular _ _ _ hY hD)))
    (scale_regular _ _ _ hZ hD)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hA : Δ ⊢[PRAAx] le one (sh a) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift
  have hAD : Δ ⊢[PRAAx] le (sh a) (sh d) := by simpa [Δ,sh,Fm.shift,Syn.shift] using had.shift
  have hDB : Δ ⊢[PRAAx] le (sh d) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hdB.shift
  have hD' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift
  simpa only [GaussianNamedRealOrderEnvelope.envelope,Syn.shift,sh,Δ,subst_centerData,subst_weightedData,subst_observationCost] using
    observation (sh a) (sh d) (sh B) (sh D) (sh r) (sh s) (var 0) hA hAD hDB hD'

end LeanProofs.IPRA.Analysis.GaussianHarmonicWeightedQuadraticName
