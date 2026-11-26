import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianNamedEulerUnitTime
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitLogarithmicTime
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse

/-!
# The original exponential recovers a named input from its unit time

Both sides execute the original arithmetic programs. The comparison at
precision p uses the original rational time at the fraction decoded from
f(p). The finite exponential Lipschitz estimate is uniform in that
fraction. A finite gap query removes the resulting diagonal allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitTimeExponential

open_ipra
open GaussianNamedEulerUnitTime (source original_bound encoded_source encodedTime original_frozen_rate)
open GaussianEulerUnitLogarithmicMargin (timeF timeData)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianNameRingLaws (negativeF negativeData negative_at)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRadiusExponentialName (input inputPrecision query value sample)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianGammaCanonicalExponent (constantF constant_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev inputF (f : PR 2) : PR 2 := negativeF (GaussianNamedEulerUnitTime.nameF f)
def inputData (x E : PTm n) : PTm n := negativeData (GaussianNamedEulerUnitTime.data x E)
abbrev nameF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (inputF f)
def data (x E : PTm n) : PTm n := GaussianRadiusExponentialName.data E (inputData x E)
def budget (E : PTm n) : PTm n := factor E*(E+two)+two

ipra_subst inputData
ipra_subst data
ipra_subst budget

theorem time_input (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    input (GaussianNamedEulerUnitTime.nameF f) E (GaussianNamedEulerUnitTime.data x E) := by
  refine .andI (GaussianNamedEulerUnitTime.name_regular f x E h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianNamedEulerUnitTime.subst_data,Syn.shift] using
    original_bound f (var 0) (Syn.shift x) (Syn.shift E) hs

theorem negative_input (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    input (inputF f) E (inputData x E) :=
  GaussianExponentialInverse.negative_input _ _ _ (time_input f x E h)

private theorem harmonic_input (a b E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source a b E) : Γ ⊢[PRAAx]
    input timeF E (timeData a b) := by
  refine .andI (GaussianEulerUnitLogarithmicMargin.time_regular a b h.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source (Syn.shift a) (Syn.shift b) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerUnitLogarithmicMargin.subst_timeData,Syn.shift] using
    GaussianNamedEulerUnitTime.harmonic_time_bound (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) hs

private theorem rational_recovery (a b E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source a b E) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerUnitLogarithmicTime.exponentialF constantF
      (GaussianRadiusExponentialName.data E (negativeData (timeData a b)))
      (GaussianPositiveRationalLogarithm.fraction a b) := by
  have changeRadius := GaussianExponentialRadiusIndependence.same_input_cross
    GaussianEulerUnitLogarithmicTime.negativeTimeF E (GaussianEulerUnitLogarithmicTime.radius a b)
    (GaussianEulerUnitLogarithmicTime.negativeTimeData a b)
    (GaussianExponentialInverse.negative_input _ _ _ (harmonic_input a b E h))
    (GaussianEulerUnitLogarithmicTime.negative_time_input a b h.andE₁)
  exact cross_trans _ _ _ _ _ _ changeRadius
    (GaussianEulerUnitLogarithmicTime.original_exponential_recovers_unit_fraction a b h.andE₁)

private theorem negative_recode (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF f) p (negativeData x) ≐ GaussianFastValueCut.recode
      (qnegative (ap2 f (GaussianFastValueCut.exponent (one+one) p) x)) :=
  (negative_at f x p).eqTrans (GaussianNameArithmetic.recode_congr
    (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)))

private theorem sample_to_frozen (f : PR 2) (p x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x E))
      (sample GaussianEulerUnitLogarithmicTime.negativeTimeF E p (negativeData (encodedTime f p x)))
      (factor E*(E+two)) (unit p) := by
  let t := inputPrecision E p
  let r := GaussianFastValueCut.exponent (one+one) t
  let y := encodedTime f p x
  have ht : Γ ⊢[PRAAx] le p r := le_trans (GaussianRadiusExponentialLipschitzRate.original_clock_later E p) (le_add_right _ _)
  have grow := GaussianExponentialReference.unit_monotone ht
  have raw := GaussianNamedInverseRate.diagonal_rate _ _ _ _ E (unit p) r
    (unit_positive p) (original_frozen_rate f p x E h)
  have near := distance_radius_mono _ _ _ _ (E+two) (unit p)
    (positive_product _ _ (unit_positive p) (unit_positive r)) (unit_positive p)
    (by ipra_le (2*𝔞(unit p))*sl grow) raw
  have neg := GaussianNamedDifference.negative_distance _ _ _ _ (unit_positive p) near
  have qnear : Γ ⊢[PRAAx] distanceBounded (query (inputF f) E p (inputData x E))
      (query (negativeF timeF) E p (negativeData y)) (E+two) (unit p) :=
    distance_congr (negative_recode (GaussianNamedEulerUnitTime.nameF f) t _).eqSymm
      (negative_recode timeF t y).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianFastValueCut.recode_distance_bound _ _ _ _ (unit_positive p) neg)
  have rightInput := GaussianExponentialInverse.negative_input _ _ _ (harmonic_input _ _ E (encoded_source f p x E h))
  have both := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz _ _ E (E+two) (unit p)
    (GaussianRadiusExponentialName.index E p)
    (unit_positive p) (GaussianRadiusExponentialName.query_bound _ _ _ _ (negative_input f x E h))
    (GaussianRadiusExponentialName.query_bound _ _ _ _ rightInput) qnear
  exact distance_congr (GaussianRadiusExponentialName.sample_at (inputF f) E p (inputData x E)).eqSymm
    (GaussianRadiusExponentialName.sample_at (negativeF timeF) E p (negativeData y)).eqSymm (.eqRefl _) (.eqRefl _) both

theorem original_diagonal (f : PR 2) (p x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x E)) (ap2 f p x) (budget E) (unit p) := by
  let a := numerator (ap2 f p x)
  let b := denominator (ap2 f p x)
  have atRational := cross_at _ _ _ _ p p (rational_recovery a b E (encoded_source f p x E h))
  have same := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive p) (unit_positive p))
    (unit_positive p) (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) (constant_at p (GaussianPositiveRationalLogarithm.fraction a b)) (.eqRefl _) (.eqRefl _) atRational)
  have decoded := distance_radius_mono _ _ _ _ zero (unit p) (le_refl one) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianUnitIntervalInputDecoding.decoded_distance _ E (GaussianNamedEulerUnitTime.source_at f p x E h))
  have joined := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (sample_to_frozen f p x E h) same) decoded
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [budget]; ipra_ring) (.eqRefl _) joined

theorem original_recovery (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) f (data x E) x := by
  have regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (nameF f) (data x E) :=
    GaussianRadiusExponentialName.name_regular (inputF f) E (inputData x E) (negative_input f x E h)
  refine GaussianNameRingLaws.equivalent_of_envelope (nameF f) f (data x E) x (budget E) regular h.andE₁ (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_data,subst_budget,Syn.shift] using
    original_diagonal f (var 0) (Syn.shift x) (Syn.shift E) hs

theorem actual_named_exponential_recovers_unit_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source f (var 0) (var 1) ⟶ crossEquivalent (nameF f) f (data (var 0) (var 1)) (var 0)) :=
  closeUniv 2 (.impI (original_recovery f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitTimeExponential
