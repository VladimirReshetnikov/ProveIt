import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowTimePowerOrder

/-!
# The actual low-time reference is the reciprocal rational square

The checked multiplier is literally the canonical negative natural two.
Actual reciprocal harmonic samples are literal negatives, so the same
bounded product sampler becomes natural two times the reciprocal sample.
Only genuine independent-query name errors are removed before invoking
the original integer exponential theorem for the original scalar power.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowTimeReciprocalReference

open_ipra
open GaussianEulerLowTimePowerOrder (multiplier referenceData referenceExpData)
open GaussianEulerLowerPowerOrder (inputF expF radius)
open GaussianEulerLowerPowerCoefficients (amplification)
open GaussianRationalHorner (qmul qadd qadd_represents canonical_unique represents_congr)
open GaussianRationalMetric (qnegative distanceBounded)
open GaussianRationalNaturalScale (naturalPoint natScale)
open GaussianRationalConjugation (point point_represents)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_sub im_sub re_scale im_scale re_neg im_neg re_one im_one re_zero im_zero)
open ComplexLogarithmRemainder (zeroCode oneCode scale mul add neg)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev targetF : PR 2 := GaussianHarmonicIntegerExponential.originalExponentF
def targetData (a b : PTm n) : PTm n := GaussianHarmonicIntegerExponential.originalExponentData two b a
def source (a b : PTm n) : Fm PTm n := GaussianPositiveRationalLogarithm.source a b ⋏ le a b
ipra_subst targetData [two]
ipra_subst source

theorem multiplier_negative_two : Γ ⊢[PRAAx] (multiplier : PTm n) ≐ qnegative (naturalPoint two) := by
  let s : PTm n := GaussianRootAlgebra.sub zeroCode (scale one oneCode)
  let g : PTm n := ComplexLogarithmRemainder.neg (scale two oneCode)
  have c := GaussianEulerIntegrandName.coefficient_represents (Γ := Γ) zeroCode one (le_refl one)
  have sum := qadd_represents _ _ _ _ one (le_refl one) c (point_represents _ _ _ (le_refl one) c)
  have same : Γ ⊢[PRAAx] equal (add s (GaussianRationalReciprocal.conjugate s)) g := by
    apply equal_of_values
    · simp only [s,g,re_add,re_sub,re_scale,GaussianRationalReciprocal.re_conjugate,re_neg,re_one,re_zero]
      ipra_simps
      ring
    · simp only [s,g,im_add,im_sub,im_scale,GaussianRationalReciprocal.im_conjugate,im_neg,im_one,im_zero]
      ipra_simps
      ring
  exact canonical_unique _ _ g one (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalMetric.qnegative_canonical _) (le_refl one)
    (represents_congr (.eqRefl _) same (.eqRefl _) sum)
    (GaussianRationalMetric.qnegative_represents _ _ _ (GaussianRationalNaturalScale.natural_point_represents two))

theorem rebase_sample (p a b : PTm n) : Γ ⊢[PRAAx]
    qmul multiplier (GaussianHarmonicLogarithmName.sample p a b) ≐ natScale two (GaussianHarmonicLogarithmName.sample p b a) :=
  (GaussianRationalSyntheticDivision.qmul_congr multiplier_negative_two (.eqRefl _)).eqTrans
    ((GaussianEulerLowerRationalPowerReference.negative_move _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
        (GaussianEulerLowerPowerRebasing.reciprocal_sample p a b)).eqTrans
        (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm))

theorem target_source (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianHarmonicIntegerExponential.source b a a b :=
  .andI h.andE₁.andE₁ (GaussianHarmonicLogarithmPower.compact_domain b a (.andI h.andE₁.andE₂ h.andE₁.andE₁))

theorem target_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN targetF (targetData a b) :=
  GaussianHarmonicIntegerExponential.original_exponent_regular two b a a b (target_source a b h)

theorem diagonal_error (p R a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 inputF p (referenceData R a b)) (ap2 targetF p (targetData a b)) (num 4) (unit p) := by
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let t := GaussianNaturalScaleProductName.clock GaussianPositiveRationalLogarithm.logF p two (GaussianPositiveRationalLogarithm.data b a)
  have hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source b a := .andI h.andE₁.andE₂ h.andE₁.andE₁
  have raw := GaussianEulerUpperPowerCompatibility.later_cross GaussianHarmonicLogarithmName.nameF GaussianPositiveRationalLogarithm.logF
    (GaussianHarmonicLogarithmName.data b a) (GaussianPositiveRationalLogarithm.data b a) p s t (le_add_right _ _)
    (GaussianNaturalScaleProductName.clock_later _ _ _ _) (GaussianNameEquivalence.cross_symm _ _ _ _
      (GaussianHarmonicLogarithmName.cross_original b a hs))
  have scaled := GaussianNamedNaturalScale.scaled_distance two _ _ two (unit p) (GaussianPositiveRationalLogarithm.radius b a)
    (unit_positive p) raw (GaussianPositiveRationalLogarithm.sample_bound t b a hs)
  have left := (GaussianBoundedConstantProductName.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF p
    (amplification R) (multiplier : PTm n) (GaussianHarmonicLogarithmName.data a b)).eqTrans (rebase_sample s a b)
  exact distance_congr left.eqSymm (GaussianNaturalScaleProductName.product_at GaussianPositiveRationalLogarithm.logF p
    two (GaussianPositiveRationalLogarithm.data b a)).eqSymm (by ipra_ring) (.eqRefl _) scaled

theorem exponent_cross (R a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent inputF targetF (referenceData R a b) (targetData a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4)
    (GaussianEulerLowTimePowerOrder.reference_input R a b h).andE₁ (target_regular a b h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift] using diagonal_error (var 0) (Syn.shift R) (Syn.shift a) (Syn.shift b) hs

theorem exponential_reciprocal_square (R a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent expF GaussianGammaCanonicalExponent.constantF (referenceExpData R a b)
      (GaussianHarmonicIntegerExponential.rationalPower b a two) := by
  have target := GaussianGammaFiniteApproximantName.exponential_input targetF (targetData a b) (target_regular a b h)
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper inputF targetF
    (radius R b) (GaussianHarmonicIntegerExponential.originalRadius two b a)
    (referenceData R a b) (targetData a b) (GaussianEulerLowTimePowerOrder.reference_input R a b h) target (exponent_cross R a b h)
  exact cross_trans _ _ _ _ _ _ proper
    (GaussianHarmonicIntegerExponential.original_integer_exponential two b a a b (target_source a b h))

theorem actual_low_time_multiplier_negative_two_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (multiplier : PTm 0) ≐ qnegative (naturalPoint two) := multiplier_negative_two

theorem actual_low_time_reference_reciprocal_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶ crossEquivalent expF GaussianGammaCanonicalExponent.constantF
      (referenceExpData (var 0) (var 1) (var 2)) (GaussianHarmonicIntegerExponential.rationalPower (var 2) (var 1) two)) :=
  closeUniv 3 (.impI (exponential_reciprocal_square _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowTimeReciprocalReference
