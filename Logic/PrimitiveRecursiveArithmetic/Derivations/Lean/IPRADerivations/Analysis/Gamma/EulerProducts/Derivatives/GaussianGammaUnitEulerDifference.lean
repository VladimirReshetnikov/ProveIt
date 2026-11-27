import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianGammaEulerFirstDerivative
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Normalization.GaussianEulerUnitNormalization

/-!
# Positive rational increments for the original Gamma derivative at one

The actual divided difference uses the original Gamma program at one
and at the native shifted point representing 1+1/D. A computed lower
bound on D discharges the first Euler derivative hypotheses. The
denominator, quotient observation and derivative observation remain
independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaUnitEulerDifference

open_ipra
open ComplexLogarithmRemainder (oneCode normSq normSq_one)
open GaussianRationalHorner (ofGaussian ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_iff distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev quotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF gammaF gammaF
abbrev integralF : PR 2 := GaussianEulerLogarithmicImproperName.nameF
def integralData : PTm n := GaussianEulerLogarithmicImproperName.data one oneCode one one one
def quotientData (D : PTm n) : PTm n :=
  GaussianGammaEulerFirstDerivative.quotientData oneCode one one one oneCode D
def modulus (p : PTm n) : PTm n := GaussianEulerLogarithmicContinuity.modulus (p+num 6) one one one
def minimumDenominator (p : PTm n) : PTm n := modulus p+unit p

ipra_subst integralData
ipra_subst quotientData
ipra_subst modulus
ipra_subst minimumDenominator

theorem denominator_positive (p D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator p) D) : Γ ⊢[PRAAx] le one D :=
  le_trans (unit_positive p) (le_trans (le_add_left _ _) h)

theorem increment_bound (M D : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hD : Γ ⊢[PRAAx] le M D) :
    Γ ⊢[PRAAx] bounded (ofGaussian oneCode D) one M := by
  have hp : Γ ⊢[PRAAx] le one D := le_trans hM hD
  have square := AnalyticNumberTheory.PhiLower.le_mul_mono hD hD
  have left : Γ ⊢[PRAAx] M*M ≐ (M*M)*normSq (oneCode : PTm n) :=
    (Prf.eqTrans (by ipra_ring : Γ ⊢[PRAAx] M*M ≐ (M*M)*one) (congrMul (.eqRefl _) normSq_one.eqSymm))
  exact (bounded_iff _ _ _ _ _ hp hM (ofGaussian_represents oneCode D hp)).iffMpr
    (le_congr left (by ipra_ring) square)

theorem original_source (p D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator p) D) : Γ ⊢[PRAAx]
    GaussianGammaEulerFirstDerivative.source p oneCode one one one oneCode D := by
  have hm := GaussianEulerLogarithmicContinuity.modulus_positive (Γ := Γ) (p+num 6) one one one
  have hs := increment_bound (modulus p) D hm (le_trans (le_add_right _ _) h)
  exact .andI (.andI (.andI GaussianEulerUnitNormalization.unit_lower_source
    (.andI (denominator_positive p D h) hs))
    (le_congr (.eqRefl _) normSq_one.eqSymm (le_refl one))) (le_refl one)

theorem original_rate (p D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator p) D) : Γ ⊢[PRAAx]
    independentRate quotientF integralF (quotientData D) integralData one (unit p) :=
  GaussianGammaEulerFirstDerivative.original_first_derivative_rate p oneCode one one one oneCode D (original_source p D h)

theorem original_observations (p q r D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator p) D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 quotientF q (quotientData D)) (ap2 integralF r integralData)
      (rateNumerator one (unit p) q r) (rateDenominator (unit p) q r) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ q r (original_rate p D h)

theorem actual_unit_Euler_derivative_positive_steps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (minimumDenominator (var 0)) (var 1) ⟶
      independentRate quotientF integralF (quotientData (var 1)) integralData one (unit (var 0))) :=
  closeUniv 2 (.impI (original_rate _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaUnitEulerDifference
