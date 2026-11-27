import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Bounds.GaussianEulerUnitCompactTimeBounds
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Powers.GaussianEulerLowerPowerRebasing
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# Exact compact variation of the actual unit-substitution time

The original rational log has Lipschitz constant E on times at least
1/E. Actual independent-name transport gives the same rate for its
harmonic representative. Exact reciprocal harmonic samples and genuine
negation invariance then give that rate for the unchanged positive
-log(u) sampler, with two independent requested observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitTimeRate

open_ipra
open GaussianEulerUnitLogarithmicMargin (timeF timeData)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (a b c d E X Y : PTm n) : Fm PTm n := GaussianEulerUnitCompactTimeBounds.source a b E ⋏
  (GaussianEulerUnitCompactTimeBounds.source c d E ⋏ (le one Y ⋏ distanceBounded (fraction a b) (fraction c d) X Y))
ipra_subst input

theorem original_observations (p q a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 timeF p (timeData a b)) (ap2 timeF q (timeData c d))
      (rateNumerator (E*X) Y p q) (rateDenominator Y p q) := by
  have left : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b :=
    .andI h.andE₁.andE₁.andE₁ (le_trans h.andE₁.andE₁.andE₁ (le_of_lt h.andE₁.andE₁.andE₂))
  have right : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source c d :=
    .andI h.andE₂.andE₁.andE₁.andE₁ (le_trans h.andE₂.andE₁.andE₁.andE₁ (le_of_lt h.andE₂.andE₁.andE₁.andE₂))
  have old := GaussianCompactLogarithmBounds.original_log_rate a b c d E X Y left right h.andE₂.andE₂.andE₁
    h.andE₁.andE₂.andE₂.andE₁ h.andE₂.andE₁.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have harmonic := GaussianNamedRateTransport.transport logF logF GaussianHarmonicLogarithmName.nameF GaussianHarmonicLogarithmName.nameF
    (GaussianPositiveRationalLogarithm.data a b) (GaussianPositiveRationalLogarithm.data c d)
    (GaussianHarmonicLogarithmName.data a b) (GaussianHarmonicLogarithmName.data c d) (E*X) Y h.andE₂.andE₂.andE₁ old
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b left))
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original c d right))
  have raw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q harmonic
  have neg := GaussianNamedDifference.negative_distance _ _ _ _
    (GaussianNamedInverseRate.denominator_positive Y p q h.andE₂.andE₂.andE₁) raw
  exact distance_congr (GaussianEulerLowerPowerRebasing.reciprocal_sample p a b)
    (GaussianEulerLowerPowerRebasing.reciprocal_sample q c d) (.eqRefl _) (.eqRefl _) neg

theorem original_rate (a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X Y) : Γ ⊢[PRAAx]
    independentRate timeF timeF (timeData a b) (timeData c d) (E*X) Y := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b))
      (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift X)) (Syn.shift (Syn.shift Y)) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianEulerUnitLogarithmicMargin.subst_timeData,PTm.subst_mul,Syn.shift] using
    original_observations (var 1) (var 0) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) (Syn.shift (Syn.shift c))
      (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift X)) (Syn.shift (Syn.shift Y)) hs

theorem actual_unit_compact_negative_logarithm_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      independentRate timeF timeF (timeData (var 0) (var 1)) (timeData (var 2) (var 3)) (var 4*var 5) (var 6)) :=
  closeUniv 7 (.impI (original_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitTimeRate
