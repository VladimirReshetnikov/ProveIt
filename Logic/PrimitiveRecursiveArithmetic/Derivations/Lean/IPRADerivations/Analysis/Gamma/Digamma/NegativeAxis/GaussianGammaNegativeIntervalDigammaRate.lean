import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalDerivativeRate
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalQuotientNormalization

/-!
# Original negative-interval digamma rate for native unit steps

At every encoded rational between two consecutive nonpositive
integers, dividing the original Gamma unit difference quotient by
the original Gamma value converges to the literal shifted digamma.
The native step cutoff and both independent observation errors are
explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDigammaRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalDerivativeTarget (reciprocalData)
open GaussianGammaNegativeIntervalInverseStepCoefficient (step_inside)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "GF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "gd" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "S" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "sd" => GaussianGammaNegativeCriticalEndpoints.nameData
local notation "Dq" => GaussianGammaNegativeIntervalStep.data
local notation "derivativeCost" => GaussianGammaNegativeIntervalDerivativeRate.cost

def quotientF : PR 2 := multiplyF P QF
def quotientData (a b N D : PTm n) : PTm n := multiplyData P QF (reciprocalData a b N) (Dq a b N D)
def cost (a b N : PTm n) : PTm n := U P (reciprocalData a b N)*derivativeCost a b N
def minimumDenominator (p a b : PTm n) : PTm n := two*b+GaussianGammaDigammaNative.minimumDenominator p (b+a) b

theorem side_bound (p a b D : PTm n) (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] le (two*b) D :=
  le_trans (le_add_right _ _) hD

theorem original_derivative_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) : Γ ⊢[PRAAx]
    independentRate QF GF (Dq a b N D) (gd a b N) (derivativeCost a b N) (unit p) :=
  GaussianGammaNegativeIntervalDerivativeRate.original_derivative_rate p a b N D h
    (side_bound p a b D hD) (le_trans (le_add_left _ _) hD)

theorem original_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) : Γ ⊢[PRAAx]
    independentRate quotientF S (quotientData a b N D) (sd a b N) (cost a b N) (unit p) :=
  GaussianGammaNegativeIntervalQuotientNormalization.normalize_rate QF (Dq a b N D) a b N (derivativeCost a b N) (unit p) h
    (GaussianGammaNegativeIntervalStep.quotient_regular a b N D h (step_inside a b D h (side_bound p a b D hD)))
    (unit_positive p) (original_derivative_rate p a b N D h hD)

theorem actual_original_negative_interval_Gamma_derivative_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((guard (var 1) (var 2) ⋏ le (minimumDenominator (var 0) (var 1) (var 2)) (var 4)) ⟶
        independentRate QF GF (Dq (var 1) (var 2) (var 3) (var 4)) (gd (var 1) (var 2) (var 3))
          (derivativeCost (var 1) (var 2) (var 3)) (unit (var 0))) :=
  closeUniv 5 (.impI (original_derivative_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_negative_interval_digamma_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((guard (var 1) (var 2) ⋏ le (minimumDenominator (var 0) (var 1) (var 2)) (var 4)) ⟶
        independentRate quotientF S (quotientData (var 1) (var 2) (var 3) (var 4)) (sd (var 1) (var 2) (var 3))
          (cost (var 1) (var 2) (var 3)) (unit (var 0))) :=
  closeUniv 5 (.impI (original_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDigammaRate
