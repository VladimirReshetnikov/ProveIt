import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelUniformLog
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianRealNameExponentialNonnegative

/-!
# The exact linear lower bound for the original negative exponential

For a nonnegative rational `t`, the named inequality is
`1 ≤ t + exp(-t)`. Below one, the lower log rectangle proves
`log(1-t) ≤ -t`. At and above one the exponential is nonnegative.
-/

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialTangent

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaRationalFractionalChord (harmonicF)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular)
open GaussianGammaRationalWendelBoundary (fractional_full)
open GaussianGammaRationalWendelUniformLog (fractional_inverse)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameRingLaws (negativeF negativeData negative_equivalent)
open GaussianNamedGammaHalfShift (constant_sum)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (negative_order negative_constant)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero qadd)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalSyntheticDivision (qone)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingLogDuplication (exponential_regular)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order logarithm_rectangles)
open GaussianStirlingMultiplicativeBoundsOrder (exponential_order)
open RationalValueBounds (upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => harmonicF

theorem exponential_nonnegative (f : PR 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] realOrder C (E f) qzero (ed f x) := by
  apply GaussianNamedRealOrderEnvelope.order_from_envelope C (E f) qzero (ed f x) one
    (constant_regular _) (exponential_regular _ _ h)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let p : PTm (n+1) := var 0
  have h' : Δ ⊢[PRAAx] pointCN f X := by simpa [Δ,Fm.shift,Syn.shift,X] using h.shift
  have hr' : Δ ⊢[PRAAx] realSamples f X := by simpa [Δ,Fm.shift,Syn.shift,X] using hr.shift
  have e : Δ ⊢[PRAAx] fstT (ap2 C p qzero) ≐ RationalGaussianEmbedding.scalarZero :=
    (congrFst (constant_at p qzero)).eqTrans
      ((congrFst (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one)).eqSymm).eqTrans
        (GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part zero one (le_refl one)))
  have ord := GaussianRealNameExponentialNonnegative.original_observation_nonnegative f (GaussianNameBounds.U f X) X p
    (exponential_input _ _ h') hr'
  simpa [GaussianNamedRealOrderEnvelope.envelope,Syn.shift,Δ,X,p,GaussianGammaFiniteApproximantName.exponentialInputData] using
    upper_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) ord

theorem negative_fraction_real (N P : PTm n) (hP : Γ ⊢[PRAAx] le one P) :
    Γ ⊢[PRAAx] realSamples C (qsub qzero (fraction N P)) :=
  GaussianStirlingNames.constant_real _ (qsub_canonical _ _)
    (RationalGaussianEmbedding.axis_add _ _ RationalGaussianEmbedding.axis_zero
      (RationalGaussianEmbedding.axis_negative _ (GaussianStirlingNames.fraction_axis N P hP)))

theorem harmonic_inverse (a j : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent H (negativeF H) (hd a j) (negativeData (hd j a)) := by
  let x := fractionalData one one a j
  let y := fractionalData one one j a
  let z := hd j a
  have fr := fractional_full one a j (le_refl one) (.andI ha hj)
  have left := cross_symm _ _ _ _ fr
  have middle := fractional_inverse a j one one ha hj
  have right := negative_equivalent L H y z
    (fractional_regular _ _ _ _ (.andI hj ha)) (GaussianHarmonicLogarithmName.name_regular _ _ (.andI hj ha))
    (cross_to_diagonal _ _ _ _ (fractional_full one j a (le_refl one) (.andI hj ha)))
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ middle right)

theorem harmonic_exponential_fraction (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (E H) C (ed H (hd a b)) (fraction a b) := by
  let F := GaussianPositiveRationalLogarithm.logF
  let x := hd a b
  let y := GaussianPositiveRationalLogarithm.data a b
  have h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b := .andI ha hb
  have hx := GaussianHarmonicLogarithmName.name_regular a b h
  have ry := GaussianPositiveRationalLogarithm.exponential_input a b h
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper H F (GaussianNameBounds.U H x)
    (GaussianPositiveRationalLogarithm.radius a b) x y (exponential_input _ _ hx) ry
    (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b h))
  exact cross_trans _ _ _ _ _ _ left (GaussianPositiveRationalLogarithm.exponential_fraction a b h)

theorem fraction_one (p : PTm n) (hp : Γ ⊢[PRAAx] le one p) : Γ ⊢[PRAAx] fraction p p ≐ qone := by
  have e : Γ ⊢[PRAAx] fraction p p ≐ fraction (p*one) (p*one) :=
    GaussianGammaEulerMidpointLogHeadGap.fraction_congr (by ipra_ring) (by ipra_ring)
  exact e.eqTrans ((GaussianCompactRiemannSplit.fraction_cancel p one one hp (le_refl one)).eqTrans
    GaussianGammaEulerDenominator.natural_one)

theorem sum_to_one (k N P : PTm n) (hP : Γ ⊢[PRAAx] le one P) (e : Γ ⊢[PRAAx] P ≐ N+k) :
    Γ ⊢[PRAAx] qadd (fraction N P) (fraction k P) ≐ qone :=
  (GaussianStirlingOddCoefficients.fraction_add_same N k P hP).eqTrans
    ((GaussianGammaEulerMidpointLogHeadGap.fraction_congr e.eqSymm (.eqRefl P)).eqTrans (fraction_one P hP))

theorem tangent_small (N P : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hl : Γ ⊢[PRAAx] lt N P) :
    Γ ⊢[PRAAx] realOrder C (addF C (E C)) qone
      (addData (fraction N P) (ed C (qsub qzero (fraction N P)))) := by
  let k := monus P N
  let t := fraction N P
  let c := qsub qzero t
  let d := fraction k P
  let F := GaussianPositiveRationalLogarithm.logF
  let y := GaussianPositiveRationalLogarithm.data (k+N) k
  let x := hd P k
  let z := hd k P
  have hk : Γ ⊢[PRAAx] le one k := GaussianEulerUnitLogarithmicMargin.gap_positive N P hl
  have e : Γ ⊢[PRAAx] P ≐ N+k := eq_add_of_le (le_of_lt hl)
  have e' := e.eqTrans (add_comm N k)
  have hOld : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (k+N) k :=
    .andI (le_trans hk (le_add_right _ _)) hk
  have change := GaussianGammaCompactCutoffAlignment.cross_data_congr F H y y (hd (k+N) k) x
    (.eqRefl _) (congrPairT e'.eqSymm (.eqRefl k)) (GaussianHarmonicLogarithmName.cross_original _ _ hOld)
  have bound := GaussianNamedRealOrderTransport.transport C C F H t (fraction N (k+N)) y x
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianGammaEulerMidpointLogHeadGap.fraction_congr (.eqRefl N) e')) change (logarithm_rectangles k N hk).andE₁
  have hx := GaussianHarmonicLogarithmName.name_regular P k (.andI hP hk)
  have hz := GaussianHarmonicLogarithmName.name_regular k P (.andI hk hP)
  have h := negative_order C H t x (constant_regular _) hx bound
  have logOrd := GaussianNamedRealOrderTransport.transport H (negativeF H) (negativeF C) C z (negativeData x)
    (negativeData t) c (harmonic_inverse k P hk hP) (negative_constant t) h
  have expOrd := exponential_order H C z c hz (constant_regular _)
    (GaussianHarmonicLogarithmName.real_samples _ _) (negative_fraction_real N P hP) logOrd
  have small := GaussianNamedRealOrderTransport.transport C (E H) (E C) (E C) d (ed H z) (ed C c) (ed C c)
    (cross_symm _ _ _ _ (harmonic_exponential_fraction k P hk hP))
    (cross_refl _ _ (exponential_regular C c (constant_regular _))) expOrd
  have add := add_order C C C (E C) t t d (ed C c) (order_refl _ _ (constant_regular _)) small
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (constant_sum t d qone (sum_to_one k N P hP e)))
    (cross_refl _ _ (GaussianNameArithmetic.add_fast _ _ _ _ (constant_regular _) (exponential_regular C c (constant_regular _)))) add

theorem tangent_large (N P : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hl : Γ ⊢[PRAAx] le P N) :
    Γ ⊢[PRAAx] realOrder C (addF C (E C)) qone
      (addData (fraction N P) (ed C (qsub qzero (fraction N P)))) := by
  let t := fraction N P
  let c := qsub qzero t
  have oneEq := fraction_one (Γ := Γ) one (le_refl one)
  have ord := constant_order _ _ (fractions_order one one N P (le_refl _) hP
    (le_congr (by ipra_ring) (by ipra_ring) hl))
  have a := GaussianNamedRealOrderTransport.transport C C C C qone (fraction one one) t t
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ oneEq.eqSymm)
    (cross_refl _ _ (constant_regular _)) ord
  have e := add_order C C C (E C) qone t qzero (ed C c) a
    (exponential_nonnegative C c (constant_regular _) (negative_fraction_real N P hP))
  have id : Γ ⊢[PRAAx] crossEquivalent (addF C C) C (addData qone qzero) qone := constant_sum qone qzero qone ((GaussianRationalLinearProduct.qadd_zero_right _
    GaussianRationalSyntheticDivision.qone_canonical))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ id)
    (cross_refl _ _ (GaussianNameArithmetic.add_fast _ _ _ _ (constant_regular _) (exponential_regular C c (constant_regular _)))) e

theorem tangent (N P : PTm n) (hP : Γ ⊢[PRAAx] le one P) :
    Γ ⊢[PRAAx] realOrder C (addF C (E C)) qone
      (addData (fraction N P) (ed C (qsub qzero (fraction N P)))) :=
  .orE (lt_or_le N P) (tangent_small N P hP.wk Prf.hyp0) (tangent_large N P hP.wk Prf.hyp0)

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialTangent
