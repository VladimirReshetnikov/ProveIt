import IPRADerivations.Analysis.Euler.HarmonicLogarithms.Algebra.GaussianHarmonicIntervalPower
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.Algebra.GaussianHarmonicLogarithmProduct
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale

/-!
# The actual logarithm name at a numerical rational power

The finite all-exponent harmonic estimate is used at the original common
mesh. The actual natural-scaling clock is compared with the same earlier
logarithm observation by genuine point regularity. Their four-multiple
diagonal error disappears at one finite gap query. This identifies both
the actual harmonic name and the unchanged original logarithm name at
(a/b)^m, including m=0, with the existing scaled logarithm name.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmPower

open_ipra
open GaussianHarmonicLogarithmName (nameF data sample sample_at)
open GaussianHarmonicLogarithmProduct (mesh mesh_later)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_two_errors distance_triangle_same distance_radius_mono_den)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaledF : PR 2 := GaussianNamedNaturalScale.nameF nameF
def powerData (a b m : PTm n) : PTm n := data (pw a m) (pw b m)
def scaledData (a b m : PTm n) : PTm n := GaussianNamedNaturalScale.data m m (data a b)
def radius (a b : PTm n) : PTm n := GaussianHarmonicLogarithmName.radius b a
ipra_subst powerData
ipra_subst scaledData
ipra_subst radius

theorem compact_domain (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain a b b a :=
  .andI h (.andI (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl b) h.andE₁))
    (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl a) h.andE₂)))

theorem original_input (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input nameF (radius a b) (data a b) :=
  GaussianHarmonicLogarithmName.common_input a b b a h.andE₂ (compact_domain a b h)

theorem power_source (a b m : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    GaussianPositiveRationalLogarithm.source (pw a m) (pw b m) :=
  .andI (GaussianPolynomialPerturbation.power_positive a m h.andE₁) (GaussianPolynomialPerturbation.power_positive b m h.andE₂)

theorem finite_sample_error (p a b m : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p (pw a m) (pw b m)) (natScale m (sample p a b)) (two*m) (unit p) := by
  have hQ := le_trans (unit_positive (Γ := Γ) p) (mesh_later p)
  have raw := GaussianHarmonicIntervalPower.finite_power a b (mesh p) m h.andE₁ h.andE₂ hQ
  have old := distance_congr (sample_at p (pw a m) (pw b m)).eqSymm
    (GaussianRationalNaturalScale.natScale_congr (.eqRefl m) (sample_at p a b)).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono_den (unit_positive p) (mesh_later p) old

theorem actual_scale_clock_error (p a b m : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    distanceBounded (natScale m (sample p a b)) (ap2 scaledF p (scaledData a b m)) (two*m) (unit p) := by
  let s := GaussianNamedNaturalScale.clock p m
  have hf := original_input a b h
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianNamedNaturalScale.clock_later p m)
  have metric := GaussianNameEquivalence.point_at nameF (data a b) p s hf.andE₁
  have weakened : Γ ⊢[PRAAx] distanceBounded (sample p a b) (sample s a b) two (unit p) :=
    distance_two_errors _ _ _ _ _ (unit_positive p) (unit_positive s) (unit_positive p) (le_refl _) grow metric
  have raw := GaussianNamedNaturalScale.scaled_distance m _ _ two (unit p) (radius a b) (unit_positive p) weakened
    (GaussianRadiusExponentialName.bounded_samples_at nameF (radius a b) (data a b) s hf.andE₂)
  exact distance_congr (.eqRefl _) (GaussianNamedNaturalScale.sample_at nameF p m m (data a b)).eqSymm (mul_comm _ _) (.eqRefl _) raw

theorem diagonal_error (p a b m : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (powerData a b m)) (ap2 scaledF p (scaledData a b m)) (num 4*m) (unit p) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (finite_sample_error p a b m h) (actual_scale_clock_error p a b m h))

theorem harmonic_logarithm_power (a b m : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    crossEquivalent nameF scaledF (powerData a b m) (scaledData a b m) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4*m)
    (GaussianHarmonicLogarithmName.name_regular _ _ (power_source a b m h))
    (GaussianNamedNaturalScale.name_regular nameF m m (radius a b) (data a b) (original_input a b h) (le_refl m))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,scaledF,powerData,scaledData] using
    diagonal_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift m) hs

theorem original_logarithm_power (a b m : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    crossEquivalent GaussianPositiveRationalLogarithm.logF scaledF
      (GaussianPositiveRationalLogarithm.data (pw a m) (pw b m)) (scaledData a b m) :=
  cross_trans _ _ _ _ _ _ (GaussianHarmonicLogarithmName.cross_original _ _ (power_source a b m h))
    (harmonic_logarithm_power a b m h)

theorem actual_harmonic_logarithm_numerical_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianPositiveRationalLogarithm.source (var 0) (var 1) ⟶ crossEquivalent nameF scaledF
      (powerData (var 0) (var 1) (var 2)) (scaledData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (harmonic_logarithm_power _ _ _ Prf.hyp0))
theorem unchanged_original_logarithm_numerical_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianPositiveRationalLogarithm.source (var 0) (var 1) ⟶ crossEquivalent GaussianPositiveRationalLogarithm.logF scaledF
      (GaussianPositiveRationalLogarithm.data (pw (var 0) (var 2)) (pw (var 1) (var 2))) (scaledData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_logarithm_power _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmPower
