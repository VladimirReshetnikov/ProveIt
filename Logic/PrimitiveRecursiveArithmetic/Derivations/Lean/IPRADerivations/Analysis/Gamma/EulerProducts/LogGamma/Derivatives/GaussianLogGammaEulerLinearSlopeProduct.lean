import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerLinearSlope
import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# The first-order term of the finite Euler logarithm

Multiplication of the actual finite slope by the argument displacement
is equivalent to the named difference of the original weighted cutoff
logarithm and the literal finite sum of weighted reciprocals.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearSlopeProduct

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianLogGammaEulerArgumentIncrement (step weightedData weighted_regular)
open GaussianLogGammaEulerHead (productF)
open GaussianLogGammaEulerLinearSlope (linearSum sum_value)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence
  (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal diagonal_at)
open GaussianNamedDifference (difference_distance sample_error)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder
  (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "slopeF" => GaussianLogGammaEulerReciprocalSlope.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlope.data
local notation "logData" => GaussianPositiveRationalLogarithm.data
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "source" => GaussianRightHalfPlaneLogarithm.source
local notation "headF" => GaussianLogGammaEulerHead.nameF
local notation "headData" => GaussianLogGammaEulerHead.data
local notation "rowSumF" => GaussianLogGammaEulerArgumentIncrement.sumF
local notation "rowSumData" => GaussianLogGammaEulerArgumentIncrement.sumData

def nameF : PR 2 := multiplyF constantF slopeF

def data (A B neg a b sign D N : PTm n) : PTm n :=
  multiplyData constantF slopeF (step A B neg a b sign D) (slopeData A B D neg N)

def targetF : PR 2 := diffF productF constantF

def targetData (A B neg a b sign D N : PTm n) : PTm n :=
  diffData (weightedData A B neg a b sign D N) (linearSum A B neg a b sign D N)

theorem regular (A B neg a b sign D N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN nameF (data A B neg a b sign D N) :=
  multiply_fast constantF slopeF _ _ (constant_regular _)
    (GaussianLogGammaEulerReciprocalSlope.regular A B D neg N hN)

theorem target_regular (A B neg a b sign D N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN targetF (targetData A B neg a b sign D N) :=
  GaussianNamedDifference.name_regular productF constantF _ _
    (weighted_regular A B neg a b sign D N hN) (constant_regular _)

theorem equivalent (A B neg a b sign D N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent nameF targetF
      (data A B neg a b sign D N) (targetData A B neg a b sign D N) := by
  let displacement := step A B neg a b sign D
  let logarithm := logData N one
  let reciprocals := reciprocalSum A B D neg (succ N)
  let slope := slopeData A B D neg N
  let weightedSlope := data A B neg a b sign D N
  let weightedLog := weightedData A B neg a b sign D N
  let linear := linearSum A B neg a b sign D N
  let C := multiplyF constantF constantF
  let weightedReciprocals := multiplyData constantF constantF displacement reciprocals
  let recovered := addF slopeF constantF
  let recoveredData := addData slope reciprocals
  have hDisplacement := constant_regular (Γ := Γ) displacement
  have hReciprocals := constant_regular (Γ := Γ) reciprocals
  have hLogarithm := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have hSlope := GaussianLogGammaEulerReciprocalSlope.regular A B D neg N hN
  have hWeightedSlope := regular A B neg a b sign D N hN
  have hWeightedLog := weighted_regular A B neg a b sign D N hN
  have hWeightedReciprocals := multiply_fast constantF constantF displacement reciprocals
    hDisplacement hReciprocals
  have recoveredLog := GaussianGammaRationalRatioBinding.difference_add_recover logF constantF
    logarithm reciprocals hLogarithm hReciprocals
  have recoveredWeighted := multiply_cross constantF constantF recovered logF
    displacement displacement recoveredData logarithm hDisplacement hDisplacement
    (add_fast slopeF constantF slope reciprocals hSlope hReciprocals) hLogarithm
    (cross_refl constantF displacement hDisplacement) recoveredLog
  have distributed := GaussianNameRingLaws.distributive constantF slopeF constantF
    displacement slope reciprocals hDisplacement hSlope hReciprocals
  have summed : Γ ⊢[PRAAx] crossEquivalent (addF nameF C) productF
      (addData weightedSlope weightedReciprocals) weightedLog :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ distributed) recoveredWeighted
  have collapsed : Γ ⊢[PRAAx] crossEquivalent C constantF weightedReciprocals linear :=
    cross_trans _ _ _ _ _ _ (constant_product_cross displacement reciprocals)
      (constant_data_cross _ _ (sum_value A B neg a b sign D N).eqSymm)
  have reduced := difference_proper productF (addF nameF C) constantF C
    weightedLog (addData weightedSlope weightedReciprocals) linear weightedReciprocals
    hWeightedLog (add_fast nameF C _ _ hWeightedSlope hWeightedReciprocals)
    (constant_regular linear) hWeightedReciprocals
    (cross_symm _ _ _ _ summed) (cross_symm _ _ _ _ collapsed)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ reduced
    (GaussianNamedStrictOrderDifference.sum_sub_right nameF C _ _ hWeightedSlope hWeightedReciprocals))

theorem actual_finite_Euler_logarithm_weighted_slope_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8 (le one (var 7) ⟶
      crossEquivalent nameF targetF
        (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (targetData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (equivalent _ _ _ _ _ _ _ _ Prf.hyp0))

/-- At a common observation clock, a bound for the actual denominator
row sum transfers to the finite Euler increment with explicit sampler slack. -/
theorem original_increment_at (p A B neg a b sign D N E K : PTm n)
    (hBase : Γ ⊢[PRAAx] source A D neg) (hLater : Γ ⊢[PRAAx] source a D sign)
    (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K)
    (hRows : Γ ⊢[PRAAx] distanceBounded (ap2 rowSumF p (rowSumData A B neg a b sign D N))
      (linearSum A B neg a b sign D N) E K) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 headF p (headData a b D sign N)) (ap2 headF p (headData A B D neg N)))
      (ap2 nameF p (data A B neg a b sign D N)) (E*unit p+num 22*K) (K*unit p) := by
  let x := headData a b D sign N
  let y := headData A B D neg N
  let s := rowSumData A B neg a b sign D N
  let w := weightedData A B neg a b sign D N
  let l := linearSum A B neg a b sign D N
  let T := GaussianLogGammaEulerArgumentIncrement.windowF
  let t := GaussianLogGammaEulerArgumentIncrement.windowData A B neg a b sign D N
  let m := targetData A B neg a b sign D N
  let v := data A B neg a b sign D N
  let rawHead := qsub (ap2 headF p x) (ap2 headF p y)
  let rawWindow := qsub (ap2 productF p w) (ap2 rowSumF p s)
  let rawLinear := qsub (ap2 productF p w) l
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have hKU := positive_product K U hK hU
  have hx := GaussianLogGammaEulerHead.regular a b D sign N hLater hN
  have hy := GaussianLogGammaEulerHead.regular A B D neg N hBase hN
  have hw := weighted_regular A B neg a b sign D N hN
  have hs := GaussianLogGammaEulerArgumentIncrement.sum_regular A B neg a b sign D N hBase hLater
  have headSample := distance_symmetric _ _ _ _ hU (sample_error headF headF x y p hx hy)
  have headWindow := diagonal_at (diffF headF headF) T (diffData x y) t p
    (cross_to_diagonal _ _ _ _
      (GaussianLogGammaEulerArgumentIncrement.original_equivalent A B neg a b sign D N hBase hLater hN))
  have windowSample : Γ ⊢[PRAAx] distanceBounded (ap2 T p t) rawWindow (num 6) U :=
    sample_error productF rowSumF w s p hw hs
  have headToWindow := distance_triangle_same rawHead _ rawWindow _ _ U hU
    (distance_triangle_same _ _ _ _ _ U hU headSample headWindow) windowSample
  have toRawLinear : Γ ⊢[PRAAx] distanceBounded rawWindow rawLinear E K :=
    distance_congr (.eqRefl _) (.eqRefl _) (zero_add _) (.eqRefl _)
      (difference_distance _ _ _ _ _ _ K hK (distance_refl_zero (ap2 productF p w) K hK) hRows)
  have linearSample : Γ ⊢[PRAAx] distanceBounded rawLinear (ap2 targetF p m) (num 6) U :=
    distance_symmetric _ _ _ _ hU
      (distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p l)) (.eqRefl _) (.eqRefl _)
        (sample_error productF constantF w l p hw (constant_regular l)))
  have linearSlope := diagonal_at targetF nameF m v p
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (equivalent A B neg a b sign D N hN)))
  have linearToSlope := distance_triangle_same rawLinear _ _ _ _ U hU linearSample linearSlope
  have budget := GaussianReconstructionRoots.distance_triangle rawWindow rawLinear _ E K _ U hK hU
    toRawLinear linearToSlope
  have comparison := GaussianReconstructionRoots.distance_triangle rawHead rawWindow _ _ U _ (K*U) hU hKU
    headToWindow budget
  exact distance_radius_mono _ _ _ _ _ _ (positive_product U (K*U) hU hKU) hKU
    (le_of_eq_add (d := zero) (by ipra_ring)) comparison

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearSlopeProduct
