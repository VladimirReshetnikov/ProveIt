import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBoundsShiftCorrection
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRecurrence

/-!
# Exact decomposition of the translated Stirling difference

The change in the original Stirling name between an integer and the
adjacent rational argument is the sum of the logarithmic gamma
increment error and the elementary logarithmic correction.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsShiftAlgebra

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_diagonal_at)
open GaussianNameRingLaws (add_sample_error multiply_sample_error through_identity)
open GaussianNamedDifference (difference_distance)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qmul positive_product ofGaussian_represents represents represents_congr
  represents_rescale canonical_unique qadd_canonical qadd_represents qmul_represents)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qsub_represents qsub_canonical distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr rescale_to)
open GaussianRootAlgebra (equal equal_of_values sub re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale re_one im_one)
open GaussianStirlingDifferenceAlgebra (rawA)
open GaussianStirlingGlobalBoundsShiftArguments
  (shiftedNumerator shifted_positive positiveFraction ratioData log_ratio_regular
    deltaF deltaData delta_regular slopeF slopeData slope_regular shifted_log)
open GaussianStirlingGlobalBoundsShiftCorrection
  (correctionF correctionData correction_regular product_regular point_at_double_scale offset_represents)
open GaussianStirlingNames (nameData name_regular source point offset logXF logXData log_x_regular
  logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "A" => GaussianStirlingNames.nameF
local notation "P" => GaussianStirlingGlobalBoundsShiftCorrection.productF
local notation "PD" => GaussianStirlingGlobalBoundsShiftCorrection.productData
local notation "aBudget" => GaussianStirlingRecurrence.aBudget
local notation "three" => GaussianNameRingLaws.three

def rawCorrection (i r b y : PTm n) : PTm n := qsub (positiveFraction r b) (qmul (offset (shiftedNumerator i r b) b) y)
def rawSlopeResidual (r b g h l : PTm n) : PTm n := qsub (qsub g h) (qmul (positiveFraction r b) l)

theorem exact_difference (i r b g h l y : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qsub (rawA (shiftedNumerator i r b) b g (qadd l y)) (rawA i one h l)
      ≐ qadd (rawSlopeResidual r b g h l) (rawCorrection i r b y) := by
  let j := shiftedNumerator i r b
  let D := (rawDen g*rawDen h)*(rawDen l*rawDen y)
  let C := two*b
  let E := C*D
  let G := scale (rawDen h*rawDen l*rawDen y) (rawGaussian g)
  let H := scale (rawDen g*rawDen l*rawDen y) (rawGaussian h)
  let L := scale (rawDen g*rawDen h*rawDen y) (rawGaussian l)
  let Y := scale (rawDen g*rawDen h*rawDen l) (rawGaussian y)
  let x := scale two (scale j oneCode)
  let v := scale b (scale two (scale i oneCode))
  let u := scale two (scale r oneCode)
  let m := sub x (scale b (scale one oneCode))
  let k := scale b (sub (scale two (scale i oneCode)) (scale one (scale one oneCode)))
  have hc : Γ ⊢[PRAAx] le one C := positive_product _ _ RationalAlgebra.two_positive hb
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (raw_den_positive g) (raw_den_positive h))
    (positive_product _ _ (raw_den_positive l) (raw_den_positive y))
  have he := positive_product _ _ hc hd
  have rg : Γ ⊢[PRAAx] represents g G D := rescale_to _ _ _ _ _ (raw_represents g) (by unfold D; ipra_ring)
  have rh : Γ ⊢[PRAAx] represents h H D := rescale_to _ _ _ _ _ (raw_represents h) (by unfold D; ipra_ring)
  have rl : Γ ⊢[PRAAx] represents l L D := rescale_to _ _ _ _ _ (raw_represents l) (by unfold D; ipra_ring)
  have ry : Γ ⊢[PRAAx] represents y Y D := rescale_to _ _ _ _ _ (raw_represents y) (by unfold D; ipra_ring)
  have reG := rescale_to g G D C E rg (mul_comm _ _)
  have reH := rescale_to h H D C E rh (mul_comm _ _)
  have xu : Γ ⊢[PRAAx] represents (positiveFraction r b) u C := point_at_double_scale r b hb
  have xv : Γ ⊢[PRAAx] represents (point i one) v C :=
    rescale_to _ _ (two*one) b C (point_at_double_scale i one (le_refl one)) (by dsimp [C]; ipra_ring)
  have xx : Γ ⊢[PRAAx] represents (point j b) x C := point_at_double_scale j b hb
  have mk : Γ ⊢[PRAAx] represents (offset i one) k C :=
    rescale_to _ _ (two*one) b C (offset_represents i one (le_refl one)) (by dsimp [C]; ipra_ring)
  have mm : Γ ⊢[PRAAx] represents (offset j b) m C := offset_represents j b hb
  have prod0 := qmul_represents (offset i one) l k L C D hc hd mk rl
  have prod1 := qmul_represents (offset j b) (qadd l y) m _ C D hc hd mm
    (qadd_represents _ _ _ _ D hd rl ry)
  have left := qsub_represents _ _ _ _ E he
    (qadd_represents _ _ _ _ E he (qsub_represents _ _ _ _ E he reG prod1) (represents_rescale _ _ C D xx))
    (qadd_represents _ _ _ _ E he (qsub_represents _ _ _ _ E he reH prod0) (represents_rescale _ _ C D xv))
  have right := qadd_represents _ _ _ _ E he
    (qsub_represents _ _ _ _ E he (qsub_represents _ _ _ _ E he reG reH)
      (qmul_represents (positiveFraction r b) l u L C D hc hd xu rl))
    (qsub_represents _ _ _ _ E he (represents_rescale _ _ C D xu)
      (qmul_represents (offset j b) y m Y C D hc hd mm ry))
  apply canonical_unique _ _ _ E (qsub_canonical _ _) (qadd_canonical _ _) he (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;>
    simp only [x,v,u,k,m,j,shiftedNumerator,D,C,re_add,im_add,re_sub,im_sub,re_scale,im_scale,re_mul,im_mul,re_one,im_one] <;>
    ipra_simps <;> ring

def differenceF : PR 2 := GaussianNamedDifference.nameF A A
def differenceData (i r b : PTm n) : PTm n :=
  GaussianNamedDifference.data (nameData (shiftedNumerator i r b) b) (nameData i one)
def slopeResidualF : PR 2 := GaussianNamedDifference.nameF deltaF slopeF
def slopeResidualData (i r b : PTm n) : PTm n := GaussianNamedDifference.data (deltaData i r b) (slopeData i r b)
def splitF : PR 2 := addF slopeResidualF correctionF
def splitData (i r b : PTm n) : PTm n := addData (slopeResidualData i r b) (correctionData i r b)

ipra_subst differenceData
ipra_subst splitData [slopeResidualData]

theorem slope_residual_regular (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN slopeResidualF (slopeResidualData i r b) :=
  GaussianNamedDifference.name_regular _ _ _ _ (delta_regular i r b hi hb) (slope_regular i r b hi)

private def originalCost (i r b : PTm n) : PTm n :=
  num 6+(aBudget (shiftedNumerator i r b) b zero (two+three)+aBudget i one zero zero)
private def slopeCost (i r b : PTm n) : PTm n :=
  num 6+(num 6+(multiplyModulus constantF logXF (positiveFraction r b) (logXData i one)+one))
private def correctionCost (i r b : PTm n) : PTm n :=
  num 6+(zero+(multiplyModulus constantF logF (offset (shiftedNumerator i r b) b) (ratioData i r b)+one))
private def splitCost (i r b : PTm n) : PTm n := three+(slopeCost i r b+correctionCost i r b)

@[simp] private theorem subst_originalCost {l : ℕ} (σ : Fin n → PTm l) (i r b : PTm n) :
    Syn.subst σ (originalCost i r b) = originalCost (Syn.subst σ i) (Syn.subst σ r) (Syn.subst σ b) := by
  simp [originalCost,GaussianStirlingRecurrence.aBudget,GaussianStirlingRecurrence.scaleBudget,GaussianNameArithmetic.multiplyModulus,GaussianNameRingLaws.three,one,two]
@[simp] private theorem subst_splitCost {l : ℕ} (σ : Fin n → PTm l) (i r b : PTm n) :
    Syn.subst σ (splitCost i r b) = splitCost (Syn.subst σ i) (Syn.subst σ r) (Syn.subst σ b) := by
  simp [splitCost,slopeCost,correctionCost,GaussianNameArithmetic.multiplyModulus,positiveFraction,GaussianNameRingLaws.three,one,two]

private theorem original_error (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceData i r b))
      (qsub (rawA (shiftedNumerator i r b) b (ap2 logGammaF p (logGammaData (shiftedNumerator i r b) b))
        (qadd (ap2 logXF p (logXData i one)) (ap2 logF p (ratioData i r b))))
        (rawA i one (ap2 logGammaF p (logGammaData i one)) (ap2 logXF p (logXData i one))))
      (originalCost i r b) (unit p) := by
  let j := shiftedNumerator i r b
  let g := ap2 logGammaF p (logGammaData j b)
  let h := ap2 logGammaF p (logGammaData i one)
  let l := ap2 logXF p (logXData i one)
  let t := ap2 logF p (ratioData i r b)
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have sj : Γ ⊢[PRAAx] source j b := .andI (shifted_positive _ _ _ hi hb) hb
  have si : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have logS := shifted_log i r b hi hb
  have er := distance_triangle_same _ _ _ _ _ _ hp (cross_diagonal_at p logS)
    (add_sample_error logXF logF (logXData i one) (ratioData i r b) p (log_x_regular i one si) (log_ratio_regular i r b hi hb))
  have upper := GaussianStirlingRecurrence.a_error p j b g (qadd l t) _ _ sj (distance_refl_zero g _ hp) er
  have lower := GaussianStirlingRecurrence.a_error p i one h l _ _ si (distance_refl_zero h _ hp) (distance_refl_zero l _ hp)
  have out := GaussianNamedDifference.sample_error A A (nameData j b) (nameData i one) p (name_regular j b sj) (name_regular i one si)
  exact distance_triangle_same _ _ _ _ _ _ hp out (difference_distance _ _ _ _ _ _ _ hp upper lower)

private theorem split_error (i r b p : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 splitF p (splitData i r b))
      (qadd (rawSlopeResidual r b (ap2 logGammaF p (logGammaData (shiftedNumerator i r b) b))
        (ap2 logGammaF p (logGammaData i one)) (ap2 logXF p (logXData i one)))
        (rawCorrection i r b (ap2 logF p (ratioData i r b))))
      (splitCost i r b) (unit p) := by
  let j := shiftedNumerator i r b
  let c := positiveFraction r b
  let k := offset j b
  let l := ap2 logXF p (logXData i one)
  let t := ap2 logF p (ratioData i r b)
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have hi' : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hj' : Γ ⊢[PRAAx] source j b := .andI (shifted_positive _ _ _ hi hb) hb
  have d := GaussianNamedDifference.sample_error logGammaF logGammaF (logGammaData j b) (logGammaData i one) p
    (log_gamma_regular j b hj') (log_gamma_regular i one hi')
  have s := multiply_sample_error constantF logXF c (logXData i one) p (constant_regular c) (log_x_regular i one hi')
  have s' := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _) s
  have f := GaussianNamedDifference.sample_error deltaF slopeF (deltaData i r b) (slopeData i r b) p
    (delta_regular i r b hi hb) (slope_regular i r b hi)
  have fd := distance_triangle_same _ _ _ _ _ _ hp f (difference_distance _ _ _ _ _ _ _ hp d s')
  have v := multiply_sample_error constantF logF k (ratioData i r b) p (constant_regular k) (log_ratio_regular i r b hi hb)
  have v' := distance_congr (.eqRefl _) (qmul_congr (constant_at p k) (.eqRefl _)) (.eqRefl _) (.eqRefl _) v
  have w := GaussianNamedDifference.sample_error constantF P c (PD i r b) p (constant_regular c) (product_regular i r b hi hb)
  have dc := distance_congr (Γ := Γ) (constant_at p c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (distance_refl_zero c U hp)
  have wd := distance_triangle_same _ _ _ _ _ _ hp w (difference_distance _ _ _ _ _ _ _ hp dc v')
  have out := add_sample_error slopeResidualF correctionF (slopeResidualData i r b) (correctionData i r b) p
    (slope_residual_regular i r b hi hb) (correction_regular i r b hi hb)
  exact distance_triangle_same _ _ _ _ _ _ hp out (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hp fd wd)

theorem exact_split (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent differenceF splitF (differenceData i r b) (splitData i r b) := by
  have d := GaussianNamedDifference.name_regular A A (nameData (shiftedNumerator i r b) b) (nameData i one)
    (name_regular _ _ (.andI (shifted_positive _ _ _ hi hb) hb)) (name_regular _ _ (.andI hi (le_refl one)))
  have s := add_fast slopeResidualF correctionF (slopeResidualData i r b) (correctionData i r b)
    (slope_residual_regular i r b hi hb) (correction_regular i r b hi hb)
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (originalCost i r b+splitCost i r b) d s
  refine .allI ?_
  let sh (z : PTm n) := Syn.shift z
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hi' : Δ ⊢[PRAAx] le one (sh i) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hi.shift
  have hb' : Δ ⊢[PRAAx] le one (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hb.shift
  have left := original_error (sh i) (sh r) (sh b) p hi' hb'
  have right := split_error (sh i) (sh r) (sh b) p hi' hb'
  have e := exact_difference (sh i) (sh r) (sh b)
    (ap2 logGammaF p (logGammaData (shiftedNumerator (sh i) (sh r) (sh b)) (sh b)))
    (ap2 logGammaF p (logGammaData (sh i) one)) (ap2 logXF p (logXData (sh i) one)) (ap2 logF p (ratioData (sh i) (sh r) (sh b))) hb'
  have joined : Δ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceData (sh i) (sh r) (sh b)))
      (ap2 splitF p (splitData (sh i) (sh r) (sh b)))
      (originalCost (sh i) (sh r) (sh b)+splitCost (sh i) (sh r) (sh b)) (unit p) :=
    through_identity _ _ _ _ _ _ _ (unit_positive p) left right e
  change Δ ⊢[PRAAx] distanceBounded (ap2 differenceF p (Syn.shift (differenceData i r b)))
    (ap2 splitF p (Syn.shift (splitData i r b))) (Syn.shift (originalCost i r b+splitCost i r b)) (unit p)
  simp only [Syn.shift,subst_differenceData,subst_splitData,PTm.subst_add,subst_originalCost,subst_splitCost]
  exact joined

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsShiftAlgebra
