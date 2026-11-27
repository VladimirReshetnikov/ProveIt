import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.StepQuotients.GaussianGammaNegativeIntervalInverseStepCoefficient
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.StepQuotients.GaussianGammaNegativeIntervalStep
import IPRADerivations.Analysis.Polynomials.Coefficients.NamedCoefficients.GaussianNamedConstantCoefficientDifferenceProduct

/-!
# The actual negative Gamma quotient in inverse-product form

Apply the original C24 recurrence at both rational inputs. The shifted
positive neighbor agrees with the original positive increment program.
The exact finite inverse coefficient then gives the named quotient
product rule with its original separated increment.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseStepQuotient

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse liftedF liftedData lifted_regular original_inverse_product)
open GaussianGammaNegativeIntervalInverseStepCoefficient (neighborInverse finiteInverseCoefficient step_inside exact_inverse_step)
open GaussianGammaNegativeIntervalNative (negative_regular)
open GaussianGammaNegativeIntervalStep (numerator denominator denominator_positive neighbor_guard positive_neighbor_cross)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedConstantCoefficientDifferenceProduct (lhsF lhsData rhsF rhsData product_rule rhs_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "GD" => GaussianGammaNegativeIntervalNative.data
local notation "GP" => GaussianStirlingGammaLogarithm.gammaData
local notation "ND" => GaussianGammaDigammaStep.neighborData

def finiteF : PR 2 := rhsF gammaF gammaF
def finiteData (a b N D : PTm n) : PTm n :=
  rhsData gammaF gammaF (neighborInverse a b N D) (finiteInverseCoefficient a b N D)
    (ND (b+a) b D) (GP (b+a) b) oneCode D

ipra_subst finiteData [neighborInverse, finiteInverseCoefficient, GaussianGammaNegativeIntervalStepCoefficient.finiteCoefficient, denominator, GaussianGammaDigammaStep.neighborData, GaussianGammaDigammaStep.neighborNumerator, GaussianGammaDigammaStep.neighborDenominator]

theorem positive_neighbor_regular (a b D : PTm n)
    (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] pointCN gammaF (ND (b+a) b D) :=
  GaussianStirlingGammaLogarithm.gamma_regular _ _
    (GaussianGammaDigammaStep.neighbor_source (b+a) b D (shifted_source a b h)
      (denominator_positive h (step_inside a b D h hD)))

theorem lifted_neighbor_cross (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] crossEquivalent gammaF liftedF (GD (numerator a b D) (denominator b D) N)
      (multiplyData constantF gammaF (neighborInverse a b N D) (ND (b+a) b D)) := by
  let A := numerator a b D
  let B := denominator b D
  let C := neighborInverse a b N D
  have step := step_inside a b D h hD
  have hn := neighbor_guard a b D h step
  have e := positive_neighbor_cross a b D h step
  have c := constant_regular (Γ := Γ) C
  have moved := multiply_cross constantF constantF gammaF gammaF C C (GP (B+A) B) (ND (b+a) b D)
    c c (GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source A B hn)) (positive_neighbor_regular a b D h hD)
    (cross_refl _ _ c) e
  exact cross_trans _ _ _ _ _ _ (original_inverse_product A B N hn) moved

theorem finite_regular (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] pointCN finiteF (finiteData a b N D) :=
  rhs_regular gammaF gammaF _ _ _ _ oneCode D (positive_neighbor_regular a b D h hD)
    (GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b h))
    (GaussianGammaUnitInverseSamples.actual_step_separated D (denominator_positive h (step_inside a b D h hD)))

theorem quotient_cross (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] crossEquivalent QF finiteF (GaussianGammaNegativeIntervalStep.data a b N D) (finiteData a b N D) := by
  let A := numerator a b D
  let B := denominator b D
  let C₁ := neighborInverse a b N D
  let C₀ := inverse a b N
  let CΔ := finiteInverseCoefficient a b N D
  let x := ND (b+a) b D
  let y := GP (b+a) b
  have step := step_inside a b D h hD
  have hn := neighbor_guard a b D h step
  have hx := positive_neighbor_regular a b D h hD
  have hy := GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b h)
  have apart := GaussianGammaUnitInverseSamples.actual_step_separated D (denominator_positive h step)
  have eq : Γ ⊢[PRAAx] crossEquivalent QF (lhsF gammaF gammaF) (GaussianGammaNegativeIntervalStep.data a b N D)
      (lhsData gammaF gammaF C₁ C₀ x y oneCode D) :=
    GaussianNamedDifferenceQuotientProperness.proper gammaF liftedF gammaF liftedF (GD A B N)
      (multiplyData constantF gammaF C₁ x) (GD a b N) (liftedData a b N) oneCode D
      (negative_regular _ _ _ hn) (multiply_fast _ _ _ _ (constant_regular C₁) hx)
      (negative_regular a b N h) (lifted_regular a b N h)
      (lifted_neighbor_cross a b N D h hD) (original_inverse_product a b N h)
  exact cross_trans _ _ _ _ _ _ eq (product_rule gammaF gammaF C₁ C₀ CΔ x y oneCode D hx hy apart
    (exact_inverse_step a b N D h hD))

theorem actual_original_negative_Gamma_inverse_step_quotient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (guard (var 0) (var 1) ⟶ le (two*var 1) (var 3) ⟶
        crossEquivalent QF finiteF (GaussianGammaNegativeIntervalStep.data (var 0) (var 1) (var 2) (var 3))
          (finiteData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (quotient_cross _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseStepQuotient
