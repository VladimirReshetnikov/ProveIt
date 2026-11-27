import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCoefficients
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationPowerRate
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.OrderedNames.GaussianHarmonicLogarithmMonotoneMesh
import IPRADerivations.Analysis.Exponential.Estimates.Magnitude.GaussianRationalExponentialMagnitude

/-!
# The integer power majorant in the Gauss multiplication estimate

The harmonic representative of the limiting power uses exact ordered
logarithm samples. Its Gaussian Taylor sums are bounded by cofinal
positive real Taylor sums for (m^{m(R+1)}).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLimitMajorant

open_ipra
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianBoundedIntegerExponentialStages (scaledF stageData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGaussMultiplicationPowerRate
  (amplification multiplier multiplier_bound powerF powerData limitLogData limit_power_input exponentF exponentData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianPositiveRealArithmetic (positive)
open GaussianRadiusExponentialName (data inputPrecision index query)
open GaussianRationalExponentialMagnitude (majorized)
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalMetric (bounded qnegative qsub)
open GaussianRationalNaturalScale (naturalPoint natScale)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalReciprocal (bound_congr bounded_product power)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

abbrev logName : PR 2 := GaussianHarmonicLogarithmName.nameF
def positiveLog (m : PTm n) : PTm n := GaussianHarmonicLogarithmName.data m one
def negativeLog (m : PTm n) : PTm n := GaussianHarmonicLogarithmName.data one m
def height (R m : PTm n) : PTm n := pw m (amplification R m)
def alternativeF : PR 2 := GaussianBoundedConstantProductName.nameF logName
def alternativeData (z R B m : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data (amplification R m) (multiplier z B m) (negativeLog m)
def referenceF : PR 2 := scaledF logName
def referenceData (R m : PTm n) : PTm n :=
  stageData (amplification R m) (amplification R m) (positiveLog m)
def baseRadius (m : PTm n) : PTm n := GaussianHarmonicLogarithmName.radius one m
def referenceRadius (R m : PTm n) : PTm n := GaussianBoundedIntegerExponentialStages.radius (amplification R m) (baseRadius m)
def alternativeRadius (R m : PTm n) : PTm n := amplification R m*GaussianNameBounds.U logName (negativeLog m)
def commonRadius (R m : PTm n) : PTm n := alternativeRadius R m+referenceRadius R m
def limitF : PR 2 := GaussianRadiusExponentialName.nameF alternativeF
def limitData (z R B m : PTm n) : PTm n := data (commonRadius R m) (alternativeData z R B m)

ipra_subst positiveLog
ipra_subst negativeLog
ipra_subst height
ipra_subst alternativeData
ipra_subst referenceRadius [baseRadius]
ipra_subst commonRadius [alternativeRadius]
ipra_subst limitData

private theorem harmonic_reversal (m p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 logName p (negativeLog m) ≐ qnegative (ap2 logName p (positiveLog m)) := by
  let Q := GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock p)
  let a := RationalGaussianEmbedding.embed (GammaMeshRobinLogBridge.harmonicLog m Q)
  let b := RationalGaussianEmbedding.embed (GammaMeshRobinLogBridge.harmonicLog one Q)
  have pos : Γ ⊢[PRAAx] ap2 logName p (positiveLog m) ≐ qsub a b :=
    (GaussianHarmonicLogarithmName.sample_at p m one).eqTrans
      (GaussianPositiveRationalLogarithmProperness.original_finite_difference m one Q hm (le_refl one)).eqSymm
  have neg : Γ ⊢[PRAAx] ap2 logName p (negativeLog m) ≐ qsub b a :=
    (GaussianHarmonicLogarithmName.sample_at p one m).eqTrans
      (GaussianPositiveRationalLogarithmProperness.original_finite_difference one m Q (le_refl one) hm).eqSymm
  have congr := Prf.eqCongr (qnegative (var 0) : PTm 1) (σ := ![qsub a b])
    (σ' := ![ap2 logName p (positiveLog m)]) (fun i => by fin_cases i; exact pos.eqSymm)
  exact neg.eqTrans ((GaussianRationalDistanceOrder.reversed_difference a b).eqSymm.eqTrans
    (by simpa only [GaussianRationalMetric.subst_qnegative,Syn.subst_var,Matrix.cons_val_zero] using congr))

private theorem negative_log_regular (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN logName (negativeLog m) :=
  GaussianHarmonicLogarithmName.name_regular one m (.andI (le_refl one) hm)

private theorem log_domain (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain m one one m :=
  .andI (.andI hm (le_refl one)) (.andI (le_congr (.eqRefl _) (one_mul _).eqSymm hm)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)))

private theorem base_reference_input (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    GaussianBoundedIntegerExponentialStages.input logName (baseRadius m) (positiveLog m) (naturalPoint m) m :=
  .andI (GaussianHarmonicLogarithmName.common_input m one one m (le_refl one) (log_domain m hm))
    (.andI (GaussianHarmonicLogarithmName.original_exponential_fraction m one one m (le_refl one) (log_domain m hm))
      (GaussianNamedNaturalScale.natural_point_bound m))

private theorem reference_input (R m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input referenceF (commonRadius R m) (referenceData R m) :=
  GaussianExponentialRadiusIndependence.input_widen _ _ _ _
    (GaussianBoundedIntegerExponentialStages.stage_input logName _ _ _ _ _ _ (base_reference_input m hm) (le_refl _))
    (le_add_left _ _)

private theorem reference_cross (R m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF referenceF) constantF
      (data (commonRadius R m) (referenceData R m)) (naturalPoint (height R m)) := by
  let A := amplification R m
  let F := GaussianRadiusExponentialName.nameF referenceF
  let x := referenceData R m
  let M := height R m
  have base := GaussianBoundedIntegerExponentialStages.stage_input logName A A (baseRadius m) (positiveLog m)
    (naturalPoint m) m (base_reference_input m hm) (le_refl A)
  have h := GaussianBoundedIntegerExponential.integer_power_cross logName A (baseRadius m) (positiveLog m)
    (naturalPoint m) m (base_reference_input m hm)
  have changeRadius := GaussianExponentialRadiusIndependence.same_input_cross referenceF (commonRadius R m)
    (referenceRadius R m) x (reference_input R m hm) base
  have value : Γ ⊢[PRAAx] power (naturalPoint m) A ≐ naturalPoint M :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalReciprocal.power_canonical _ _)
      (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
      (GaussianExponentialDiskMajorant.natural_power_represents m A) (GaussianRationalNaturalScale.natural_point_represents M)
  have through := cross_trans F F constantF (data (commonRadius R m) x) (data (referenceRadius R m) x)
    (power (naturalPoint m) A) changeRadius h
  exact cross_trans F constantF constantF (data (commonRadius R m) x) (power (naturalPoint m) A)
    (naturalPoint M) through (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ value)

private theorem alternative_bound_at (z R B m p : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hc : Γ ⊢[PRAAx] bounded (multiplier z B m) (amplification R m) one) : Γ ⊢[PRAAx]
    bounded (ap2 alternativeF p (alternativeData z R B m)) (alternativeRadius R m) one := by
  let A := amplification R m
  have h := GaussianNameBounds.sample_bound logName (negativeLog m) (GaussianBoundedConstantProductName.clock p A)
    (negative_log_regular m hm)
  exact bound_congr (GaussianBoundedConstantProductName.sample_at logName p A (multiplier z B m) (negativeLog m)).eqSymm
    (.eqRefl _) (one_mul _) (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hc h)

theorem alternative_input (z R B m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input alternativeF (commonRadius R m) (alternativeData z R B m) := by
  have hc := multiplier_bound z R B m hm hB hz
  apply GaussianExponentialRadiusIndependence.input_widen _ (alternativeRadius R m) _ _ _ (le_add_right _ _)
  refine .andI (GaussianBoundedConstantProductName.name_regular logName _ _ _ (.andI (negative_log_regular m hm) hc)) (.allI ?_)
  let sh (u : PTm n) := Syn.shift u
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] bounded (multiplier (sh z) (sh B) (sh m)) (amplification (sh R) (sh m)) one := by
    simpa [Fm.shift,Syn.shift,sh] using hc.shift
  simpa [GaussianRadiusExponentialName.boundedSamples,alternativeRadius,Syn.shift,sh] using
    alternative_bound_at (sh z) (sh R) (sh B) (sh m) (var 0) ms cs

theorem limit_cross (z R B m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent powerF limitF (powerData z R B m (limitLogData m)) (limitData z R B m) := by
  let F := GaussianPositiveRationalLogarithm.logF
  let c := multiplier z B m
  let A := amplification R m
  let x := limitLogData m
  let y := negativeLog m
  have hc := multiplier_bound z R B m hm hB hz
  have hcr := constant_regular (Γ := Γ) c
  have fx := GaussianGaussMultiplicationPowerRate.limit_log_regular m hm
  have fy := negative_log_regular m hm
  have changeLog := GaussianHarmonicLogarithmName.cross_original one m (.andI (le_refl one) hm)
  have eq := GaussianNameArithmetic.multiply_equivalent constantF constantF F logName c c x y hcr hcr fx fy
    (cross_to_diagonal _ _ _ _ (cross_refl constantF c hcr)) (cross_to_diagonal _ _ _ _ changeLog)
  have left := GaussianBoundedConstantProductName.ordinary_product_identity F A c x (.andI fx hc)
  have right := GaussianBoundedConstantProductName.ordinary_product_identity logName A c y (.andI fy hc)
  have inner : Γ ⊢[PRAAx] crossEquivalent exponentF alternativeF (exponentData z R B m x) (alternativeData z R B m) :=
    cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ left eq) (cross_symm _ _ _ _ right)
  exact GaussianExponentialRadiusIndependence.independent_radii_proper exponentF alternativeF
    (GaussianGaussMultiplicationPowerRate.radius R m) (commonRadius R m)
    (exponentData z R B m x) (alternativeData z R B m)
    (limit_power_input z R B m hm hB hz) (alternative_input z R B m hm hB hz) inner

private theorem natural_real_representation (A : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (naturalPoint A)) (ZT.ofNat A) one := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) (GaussianRationalNaturalScale.natural_point_represents A).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_scale, GaussianRootAlgebra.re_one, ZT.toZ_ofNat]
  ring

private theorem reference_later (p W : PTm n) : Γ ⊢[PRAAx] le p (inputPrecision W p) :=
  GaussianRadiusExponentialLipschitzRate.original_clock_later W p

private theorem finite_majorized (z R B m p t : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hpt : Γ ⊢[PRAAx] le p t)
    (hclock : Γ ⊢[PRAAx] le
      (GaussianBoundedConstantProductName.clock (inputPrecision (commonRadius R m) p) (amplification R m)) t) : Γ ⊢[PRAAx]
    majorized (ap2 limitF p (limitData z R B m))
      (ap2 (GaussianRadiusExponentialName.nameF referenceF) t (data (commonRadius R m) (referenceData R m))) := by
  let A := amplification R m
  let W := commonRadius R m
  let s := GaussianBoundedConstantProductName.clock (inputPrecision W p) A
  let j := GaussianNamedNaturalScale.clock (inputPrecision W t) A
  let u := ap2 logName s (negativeLog m)
  let h := ap2 logName s (positiveLog m)
  let v := ap2 logName j (positiveLog m)
  let c := multiplier z B m
  let P := naturalPoint A
  let q := query alternativeF W p (alternativeData z R B m)
  let r := query referenceF W t (referenceData R m)
  have hs : Γ ⊢[PRAAx] le s j :=
    le_trans hclock (le_trans (reference_later t W) (GaussianNamedNaturalScale.clock_later _ _))
  have pH : Γ ⊢[PRAAx] positive h := GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative s m one hm
  have pV : Γ ⊢[PRAAx] positive v := GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative j m one hm
  have pP : Γ ⊢[PRAAx] positive P := GaussianPositiveRealArithmetic.positive_natural A
  have cH : Γ ⊢[PRAAx] canonical h := (GaussianHarmonicLogarithmName.sample_real s m one).andE₁
  have hU : Γ ⊢[PRAAx] majorized u h := GaussianRationalExponentialMagnitude.congr
    (harmonic_reversal m s hm).eqSymm (.eqRefl _)
    (GaussianRationalExponentialMagnitude.negative_majorized _ _
      (GaussianRationalExponentialMagnitude.positive_self h pH cH))
  have laterH := GaussianRationalExponentialMagnitude.weaken _ _ _ pH pV hU
    (GaussianHarmonicLogarithmMonotoneMesh.sample_order m one s j (le_refl one) hm hs)
  have wC := GaussianRationalExponentialMagnitude.of_representation c P A one (le_refl one) pP
    (natural_real_representation A) (multiplier_bound z R B m hm hB hz)
  have qEq : Γ ⊢[PRAAx] q ≐ qmul c u :=
    GaussianBoundedConstantProductName.sample_at logName (inputPrecision W p) A c (negativeLog m)
  have rEq : Γ ⊢[PRAAx] r ≐ qmul P v :=
    (GaussianNamedNaturalScale.sample_at logName (inputPrecision W t) A A (positiveLog m)).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product A v)
  have hR : Γ ⊢[PRAAx] positive r :=
    GaussianPositiveRealArithmetic.positive_congr rEq.eqSymm (GaussianPositiveRealArithmetic.positive_multiply P v pP pV)
  have comp := GaussianRationalExponentialMagnitude.congr qEq.eqSymm rEq.eqSymm
    (GaussianRationalExponentialMagnitude.multiply c u P v pP pV wC laterH)
  let k0 := index W p
  let k1 := index W t
  have range := GaussianRadiusExponentialName.index_monotone W p t hpt
  have small := GaussianRationalExponentialMagnitude.scalar_sum_majorized q r k0 hR comp
  have large := GaussianRationalExponentialMagnitude.weaken _ _ _
    (GaussianPositiveExponentialTermBound.positive_prefix r (succ k0) hR)
    (GaussianPositiveExponentialTermBound.positive_prefix r (succ k1) hR) small
    (GaussianPositiveExponentialTermBound.prefix_real_mono r (succ k0) (succ k1) hR ((succ_monus_succ k0 k1).eqTrans range))
  exact GaussianRationalExponentialMagnitude.congr
    (GaussianRadiusExponentialName.sample_at alternativeF W p (alternativeData z R B m)).eqSymm
    (GaussianRadiusExponentialName.sample_at referenceF W t (referenceData R m)).eqSymm large

private theorem reference_positive_at (R m t : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    positive (ap2 (GaussianRadiusExponentialName.nameF referenceF) t (data (commonRadius R m) (referenceData R m))) := by
  let A := amplification R m
  let W := commonRadius R m
  let s := inputPrecision W t
  let j := GaussianNamedNaturalScale.clock s A
  let u := ap2 logName j (positiveLog m)
  let r := query referenceF W t (referenceData R m)
  have heq : Γ ⊢[PRAAx] r ≐ qmul (naturalPoint A) u :=
    (GaussianNamedNaturalScale.sample_at logName s A A (positiveLog m)).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product A u)
  have h := GaussianPositiveRealArithmetic.positive_congr heq.eqSymm
    (GaussianPositiveRealArithmetic.positive_multiply _ _ (GaussianPositiveRealArithmetic.positive_natural A)
      (GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative j m one hm))
  exact GaussianPositiveRealArithmetic.positive_congr
    (GaussianRadiusExponentialName.sample_at referenceF W t (referenceData R m)).eqSymm
    (GaussianPositiveExponentialTermBound.positive_prefix r (succ (index W t)) h)

private theorem limit_bound_slack (z R B m p s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (ap2 limitF p (limitData z R B m)) (height R m) one two s := by
  let W := commonRadius R m
  let A := amplification R m
  let M := height R m
  let P := GaussianBoundedConstantProductName.clock (inputPrecision W p) A
  let t := p+s+P
  let y := data W (referenceData R m)
  let v := ap2 (GaussianRadiusExponentialName.nameF referenceF) t y
  have ht := unit_positive (Γ := Γ) t
  have hp : Γ ⊢[PRAAx] le p t := le_trans (le_add_right p s) (le_add_right (p+s) P)
  have hs : Γ ⊢[PRAAx] le s t := le_trans (le_add_left s p) (le_add_right (p+s) P)
  have hP : Γ ⊢[PRAAx] le P t := le_add_left P (p+s)
  have major := finite_majorized z R B m p t hm hB hz hp hP
  have close := GaussianRationalDistanceOrder.distance_congr (.eqRefl _)
    (GaussianBoundedConstantProductName.constant_at t (naturalPoint M)) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ t t (reference_cross R m hm))
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ ht ht) (le_refl one) close (GaussianNamedNaturalScale.natural_point_bound M)
  have refBound : Γ ⊢[PRAAx] bounded v (M*unit t+two) (unit t) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ ht ht) (le_refl one)) ht
      (le_of_eq_add (d := zero) (by ipra_ring)) raw
  have main := GaussianRationalExponentialMagnitude.bound_from_majorant_norm _ v _ _ ht
    (reference_positive_at R m t hm) (GaussianRadiusExponentialName.sample_canonical referenceF W t (referenceData R m))
    major refBound
  have grow : Γ ⊢[PRAAx] le (unit s) (unit t) := GaussianExponentialReference.unit_monotone hs
  have budget : Γ ⊢[PRAAx] le ((M*unit t+two)*(one*unit s)) ((M*unit s+two*one)*unit t) := by
    ipra_le 2*sl grow
  exact bounded_radius_mono _ _ _ _ _ ht
    (positive_product _ _ (le_refl one) (unit_positive s)) budget main

theorem limit_bound_at (z R B m p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (ap2 limitF p (limitData z R B m)) (height R m) one := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ two (le_refl one)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh] using hB.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using hz.shift
  simpa [GaussianRationalSlackRemoval.allSlack,Syn.shift,sh] using
    limit_bound_slack (sh z) (sh R) (sh B) (sh m) (sh p) (var 0) ms bs zs

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLimitMajorant
