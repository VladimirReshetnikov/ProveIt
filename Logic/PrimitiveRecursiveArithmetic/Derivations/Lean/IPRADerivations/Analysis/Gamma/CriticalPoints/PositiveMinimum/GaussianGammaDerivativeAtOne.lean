import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianGammaUnitRawSlope

/-!
# The original Gamma derivative at one is minus Euler–Mascheroni

The cofinal positive steps are chosen from the actual logarithmic
Euler derivative budget and the quadratic inverse budget. Observed
Gamma differences at those steps converge both to the original first
logarithmic Euler integral and to the negative of the original
Euler–Mascheroni name. Every independently requested observation of
the two names then satisfies the original exact comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDerivativeAtOne

open_ipra
open GaussianGammaUnitEulerDifference
  (quotientF quotientData integralF integralData subst_integralData minimumDenominator denominator_positive)
open GaussianGammaUnitInverseSamples (baseData neighborData shiftedSample residualBudget actual_step_separated)
open GaussianGammaUnitShiftedTaylorBound (cubic)
open GaussianGammaUnitRawSlope (rawSlope rawNegative slopeBudget)
open GaussianGammaReciprocalInverse (gammaF gamma_regular)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_sample_error equivalent_of_envelope)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_at point_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "eulerF" => GaussianGammaCanonicalExponent.gammaF

abbrev negativeGammaF : PR 2 := negativeF eulerF
def negativeGammaData : PTm n := negativeData zero
def stepDenominator (s : PTm n) : PTm n := minimumDenominator s+slopeBudget*unit s
def clockCoefficient (D : PTm n) : PTm n := cubic D+residualBudget D*(D*D)+D+one
def sampleIndex (s : PTm n) : PTm n := GaussianFastValueCut.exponent (clockCoefficient (stepDenominator s)) s

ipra_subst negativeGammaData

theorem negativeGamma_regular : Γ ⊢[PRAAx] pointCN negativeGammaF (negativeGammaData : PTm n) :=
  negative_fast eulerF zero GaussianGammaCanonicalExponent.gamma_regular

theorem clock_budgets (s : PTm n) : Γ ⊢[PRAAx]
    le (cubic (stepDenominator s)) (unit (sampleIndex s)) ⋏
      (le (residualBudget (stepDenominator s)*(stepDenominator s*stepDenominator s)) (unit (sampleIndex s)) ⋏
        le (stepDenominator s*unit s) (unit (sampleIndex s))) := by
  let D := stepDenominator s
  let C := clockCoefficient D
  let U := unit s
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have paid := GaussianFastValueCut.query_budget (Γ := Γ) C s
  have all : Γ ⊢[PRAAx] le C (unit (sampleIndex s)) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right C hU)) paid
  have cube : Γ ⊢[PRAAx] le (cubic D) C :=
    le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)
  have inv : Γ ⊢[PRAAx] le (residualBudget D*(D*D)) C :=
    le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) (le_add_right _ _)
  have step : Γ ⊢[PRAAx] le D C := le_trans (le_add_left _ _) (le_add_right _ _)
  exact .andI (le_trans cube all) (.andI (le_trans inv all) (le_trans (mul_le_mul_right U step) paid))

private theorem raw_quotient_to_slope (t D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianNamedDifferenceQuotient.raw gammaF gammaF t t (neighborData D) baseData oneCode D)
      (rawSlope t D) (two*D) (unit t) := by
  let g := shiftedSample t D
  let b := ap2 gammaF t (baseData : PTm n)
  let inv := GaussianNamedDifferenceQuotient.inverse oneCode D
  have hU := unit_positive (Γ := Γ) t
  have same := GaussianNameConjugation.equal_distance g g (unit t) hU (.eqRefl g)
  have base := GaussianGammaUnitInverseSamples.original_base_observation (Γ := Γ) t
  have smaller : Γ ⊢[PRAAx] distanceBounded (GaussianRationalMetric.qsub g b) (GaussianRationalMetric.qsub g qone) two (unit t) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hU same base)
  have sep := actual_step_separated D hD
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifferenceQuotient.scale_distance inv _ _ D two (unit t) hU
      (GaussianNamedDifferenceQuotient.inverse_bound oneCode D sep) smaller)

private theorem quotient_to_slope (s t D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D)
    (ht : Γ ⊢[PRAAx] le (D*unit s) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 quotientF s (quotientData D)) (rawSlope t D) (num 5) (unit s) := by
  let U := unit s
  let T := unit t
  let raw := GaussianNamedDifferenceQuotient.raw gammaF gammaF t t (neighborData D) baseData oneCode D
  have hp := denominator_positive s D h
  have hU := unit_positive (Γ := Γ) s
  have hT := unit_positive (Γ := Γ) t
  have read := GaussianNamedDifferenceQuotient.independent_readback gammaF gammaF s t t
    (neighborData D) baseData oneCode D
    (.andI (GaussianGammaUnitInverseSamples.neighbor_regular s D h)
      (.andI (gamma_regular _ _ _ _ _ GaussianGammaUnitInverseSamples.original_base_source) (actual_step_separated D hp)))
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 quotientF s (quotientData D)) raw (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedDifferenceQuotient.denominator_positive s t t) hU
      (by unfold GaussianNamedDifferenceQuotient.numerator GaussianNamedDifferenceQuotient.denominator
          dsimp only [U,T]
          ipra_le 2*𝔞 (unit s)*𝔞 (unit t)*sl ht) read
  have last : Γ ⊢[PRAAx] distanceBounded raw (rawSlope t D) two U :=
    distance_radius_mono _ _ _ _ _ _ hT hU (by dsimp only [U,T]; ipra_le 2*sl ht) (raw_quotient_to_slope t D hp)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first last)

private theorem negative_observation_error (s t : PTm n) (h : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (rawNegative t) (ap2 negativeGammaF s negativeGammaData) (num 5) (unit s) := by
  let U := unit s
  let T := unit t
  let point := ap2 negativeGammaF t negativeGammaData
  have hU := unit_positive (Γ := Γ) s
  have hT := unit_positive (Γ := Γ) t
  have grow : Γ ⊢[PRAAx] le (unit s) (unit t) := GaussianExponentialReference.unit_monotone h
  have first : Γ ⊢[PRAAx] distanceBounded (rawNegative t) point (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ hT hU (by dsimp only [U,T,GaussianNameRingLaws.three]; ipra_le 3*sl grow)
      (distance_symmetric _ _ _ _ hT (negative_sample_error eulerF zero t GaussianGammaCanonicalExponent.gamma_regular))
  have last : Γ ⊢[PRAAx] distanceBounded point (ap2 negativeGammaF s negativeGammaData) two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hT hU) hU
      (by dsimp only [U,T]; ipra_le 𝔞 (unit s)*sl grow) (point_at _ _ t s negativeGamma_regular)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first last)

theorem original_diagonal (s : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 integralF s integralData) (ap2 negativeGammaF s negativeGammaData) (num 14) (unit s) := by
  let D := stepDenominator s
  let t := sampleIndex s
  let U := unit s
  have hU := unit_positive (Γ := Γ) s
  have hD : Γ ⊢[PRAAx] le (minimumDenominator s) D := le_add_right _ _
  have hp := denominator_positive s D hD
  have budgets := clock_budgets (Γ := Γ) s
  have late : Γ ⊢[PRAAx] le s t := le_add_right _ _
  have original := GaussianGammaUnitEulerDifference.original_observations s s s D hD
  have den : Γ ⊢[PRAAx] le one (rateDenominator U s s) := GaussianNamedInverseRate.denominator_positive _ _ _ hU
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 integralF s integralData) (ap2 quotientF s (quotientData D)) (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ den hU
      (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; dsimp only [U]; ipra_ring))
      (distance_symmetric _ _ _ _ den original)
  have second := quotient_to_slope s t D hD budgets.andE₂.andE₂
  have cutoff : Γ ⊢[PRAAx] le (slopeBudget*U) D := le_add_left _ _
  have third : Γ ⊢[PRAAx] distanceBounded (rawSlope t D) (rawNegative t) one U :=
    distance_radius_mono _ _ _ _ _ _ hp hU (le_congr (.eqRefl _) (by ipra_ring) cutoff)
      (GaussianGammaUnitRawSlope.original_raw_slope s t D hD budgets.andE₁ budgets.andE₂.andE₁)
  have fourth := negative_observation_error s t late
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU
      (distance_triangle_same _ _ _ _ _ _ hU first second) third) fourth)

theorem original_logarithmic_integral_one_is_negative_gamma : Γ ⊢[PRAAx]
    crossEquivalent integralF negativeGammaF (integralData : PTm n) negativeGammaData := by
  apply equivalent_of_envelope _ _ _ _ (num 14)
    (GaussianEulerLogarithmicImproperName.name_regular one oneCode one one one GaussianEulerUnitNormalization.unit_lower_source)
    negativeGamma_regular
  have left : Syn.shift (integralData : PTm n) = (integralData : PTm (n+1)) :=
    subst_integralData _
  have right : Syn.shift (negativeGammaData : PTm n) = (negativeGammaData : PTm (n+1)) :=
    subst_negativeGammaData _
  have constant : Syn.shift (num 14 : PTm n) = (num 14 : PTm (n+1)) := by
    simp only [Syn.shift,LeanProofs.IPRA.PTm.num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  refine .allI ?_
  change Γ.map Fm.shift ⊢[PRAAx]
    distanceBounded (ap2 integralF (var 0) (Syn.shift (integralData : PTm n)))
      (ap2 negativeGammaF (var 0) (Syn.shift (negativeGammaData : PTm n)))
      (Syn.shift (num 14 : PTm n)) (unit (var 0))
  rw [left,right,constant]
  exact original_diagonal (Γ := Γ.map Fm.shift) (var 0)

theorem original_derivative_at_one_for_increment (s h D : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianGammaEulerFirstDerivative.source s oneCode one one one h D) : Γ ⊢[PRAAx]
    independentRate quotientF negativeGammaF
      (GaussianGammaEulerFirstDerivative.quotientData oneCode one one one h D) negativeGammaData one (unit s) := by
  have regular := GaussianGammaEulerFirstDerivative.quotient_regular s oneCode one one one h D hs
  exact GaussianNamedRateTransport.transport quotientF integralF quotientF negativeGammaF _ _ _ _ one (unit s)
    (unit_positive s) (GaussianGammaEulerFirstDerivative.original_first_derivative_rate s oneCode one one one h D hs)
    (cross_refl _ _ regular) (cross_symm _ _ _ _ original_logarithmic_integral_one_is_negative_gamma)

theorem original_derivative_at_one (s D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D) : Γ ⊢[PRAAx]
    independentRate quotientF negativeGammaF (quotientData D) negativeGammaData one (unit s) :=
  original_derivative_at_one_for_increment s oneCode D (GaussianGammaUnitEulerDifference.original_source s D h)

theorem actual_original_first_logarithmic_Euler_integral_at_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent integralF negativeGammaF (integralData : PTm 0) negativeGammaData :=
  original_logarithmic_integral_one_is_negative_gamma

theorem actual_original_Gamma_derivative_at_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (minimumDenominator (var 0)) (var 1) ⟶
      independentRate quotientF negativeGammaF (quotientData (var 1)) negativeGammaData one (unit (var 0))) :=
  closeUniv 2 (.impI (original_derivative_at_one _ _ Prf.hyp0))

theorem actual_original_Gamma_derivative_at_one_for_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaEulerFirstDerivative.source (var 0) oneCode one one one (var 1) (var 2) ⟶
      independentRate quotientF negativeGammaF
        (GaussianGammaEulerFirstDerivative.quotientData oneCode one one one (var 1) (var 2)) negativeGammaData one (unit (var 0))) :=
  closeUniv 3 (.impI (original_derivative_at_one_for_increment _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDerivativeAtOne
