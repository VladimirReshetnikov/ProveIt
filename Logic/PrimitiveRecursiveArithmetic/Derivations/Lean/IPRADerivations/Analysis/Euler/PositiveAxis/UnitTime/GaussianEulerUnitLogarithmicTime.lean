import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitLogarithmicMargin
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerPowerRebasing
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence

/-!
# The actual unit-substitution time is the original negative logarithm

Exact reciprocal harmonic samples identify the positive time name with
the unchanged normalized negative of the original log(a/b). The actual
exponential of its normalized negative recovers the original fraction
u=a/b. All name operations, radii and observation clocks are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicTime

open_ipra
open GaussianEulerUnitLogarithmicMargin (source timeF timeData time_regular)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianHarmonicLogarithmName (sample)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_at)
open GaussianRationalMetric (distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def negativeTimeData (a b : PTm n) : PTm n := negativeData (timeData a b)
abbrev negativeTimeF : PR 2 := negativeF timeF
def radius (a b : PTm n) : PTm n := GaussianNameBounds.U negativeTimeF (negativeTimeData a b)
abbrev exponentialF : PR 2 := GaussianRadiusExponentialName.nameF negativeTimeF
def exponentialData (a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius a b) (negativeTimeData a b)

ipra_subst negativeTimeData
ipra_subst radius
ipra_subst exponentialData

theorem original_positive_source (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianPositiveRationalLogarithm.source a b := .andI h.andE₁ (le_trans h.andE₁ (le_of_lt h.andE₂))

/-- The actual negative-name observation is the actual reciprocal
harmonic observation at its OWN original normalization query. -/
theorem negative_harmonic_sample (p a b : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF GaussianHarmonicLogarithmName.nameF) p (negativeData (GaussianHarmonicLogarithmName.data a b)) ≐
      sample (GaussianFastValueCut.exponent (one+one) p) b a := by
  let r := GaussianFastValueCut.exponent (one+one) p
  have same : Γ ⊢[PRAAx] qsub qzero (sample r a b) ≐ sample r b a :=
    (GaussianRationalSyntheticDivision.qzero_add _ (qnegative_canonical _)).eqTrans
      (GaussianEulerLowerPowerRebasing.reciprocal_sample r a b)
  exact (GaussianNameRingLaws.negative_at GaussianHarmonicLogarithmName.nameF (GaussianHarmonicLogarithmName.data a b) p).eqTrans
    ((GaussianNameArithmetic.recode_congr same).eqTrans (GaussianExponentialReference.recode_fixed _ (GaussianHarmonicLogarithmName.sample_real r b a).andE₁))

theorem harmonic_negative_cross (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    crossEquivalent (negativeF GaussianHarmonicLogarithmName.nameF) GaussianHarmonicLogarithmName.nameF
      (negativeData (GaussianHarmonicLogarithmName.data a b)) (GaussianHarmonicLogarithmName.data b a) := by
  have original := GaussianHarmonicLogarithmName.name_regular a b h
  have reciprocal := GaussianHarmonicLogarithmName.name_regular b a (.andI h.andE₂ h.andE₁)
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ two (negative_fast _ _ original) reciprocal
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  let r : PTm (n+1) := GaussianFastValueCut.exponent (one+one) (var 0)
  have hr : Γ.map Fm.shift ⊢[PRAAx] le (unit (var 0)) (unit r) :=
    GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have near := GaussianNameEquivalence.point_at GaussianHarmonicLogarithmName.nameF
    (GaussianHarmonicLogarithmName.data (Syn.shift b) (Syn.shift a)) r (var 0)
    (GaussianHarmonicLogarithmName.name_regular _ _ (.andI hs.andE₂ hs.andE₁))
  have weak := distance_radius_mono _ _ _ _ two (unit (var 0))
    (positive_product _ _ (unit_positive r) (unit_positive (var 0))) (unit_positive (var 0))
    (by ipra_le (Groth.ι (Q.mk (Γ.map Fm.shift) (unit (var 0))))*sl hr) near
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNameRingLaws.subst_negativeData,
    GaussianHarmonicLogarithmName.subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    distance_congr (negative_harmonic_sample (var 0) (Syn.shift a) (Syn.shift b)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) weak

/-- The time used by the actual outer log is exactly the original
negative logarithm of the original unit-interval fraction. -/
theorem original_negative_logarithm (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent timeF (negativeF GaussianPositiveRationalLogarithm.logF) (timeData a b)
      (negativeData (GaussianPositiveRationalLogarithm.data a b)) := by
  have hp := original_positive_source a b h
  have original := GaussianPositiveRationalLogarithm.name_regular a b hp
  have harmonic := GaussianHarmonicLogarithmName.name_regular a b hp
  have both := GaussianNameRingLaws.negative_equivalent GaussianPositiveRationalLogarithm.logF GaussianHarmonicLogarithmName.nameF
    (GaussianPositiveRationalLogarithm.data a b) (GaussianHarmonicLogarithmName.data a b) original harmonic
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b hp))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (harmonic_negative_cross a b hp)) (cross_symm _ _ _ _ both)

theorem negative_time_input (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input negativeTimeF (radius a b) (negativeTimeData a b) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _ (negative_fast timeF (timeData a b) (time_regular a b h))

theorem original_exponential_recovers_unit_fraction (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent exponentialF GaussianGammaCanonicalExponent.constantF (exponentialData a b) (GaussianPositiveRationalLogarithm.fraction a b) := by
  have hp := original_positive_source a b h
  have inner := cross_trans _ _ _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b hp)
    (cross_symm _ _ _ _ (harmonic_negative_cross b a (.andI hp.andE₂ hp.andE₁)))
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper GaussianPositiveRationalLogarithm.logF negativeTimeF
    (GaussianPositiveRationalLogarithm.radius a b) (radius a b) (GaussianPositiveRationalLogarithm.data a b) (negativeTimeData a b)
    (GaussianPositiveRationalLogarithm.exponential_input a b hp) (negative_time_input a b h) inner
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ proper) (GaussianPositiveRationalLogarithm.exponential_fraction a b hp)

theorem actual_unit_substitution_negative_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent timeF (negativeF GaussianPositiveRationalLogarithm.logF)
      (timeData (var 0) (var 1)) (negativeData (GaussianPositiveRationalLogarithm.data (var 0) (var 1)))) :=
  closeUniv 2 (.impI (original_negative_logarithm _ _ Prf.hyp0))

theorem actual_unit_substitution_exponential_recovers_fraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent exponentialF GaussianGammaCanonicalExponent.constantF
      (exponentialData (var 0) (var 1)) (GaussianPositiveRationalLogarithm.fraction (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_exponential_recovers_unit_fraction _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicTime
