import IPRADerivations.Analysis.Stirling.GaussianStirlingConstantIdentificationCore
import IPRADerivations.Analysis.Stirling.GaussianStirlingDuplicationResidual
import IPRADerivations.Analysis.Stirling.GaussianStirlingHalfStep

/-!
# Identification of the original Stirling constant

The cofinal integer limit of the original Stirling expression is the
original name for half the logarithm of twice Pi. The proof uses the
original duplication identity and the checked half-step and residual
estimates to identify the two names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingConstantIdentification

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingConstantIdentificationCore (HalfStepBound ResidualBound sample_budget_value)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem half_step : HalfStepBound 64 :=
  fun p r x h => GaussianStirlingHalfStep.half_step_error p r x h

private theorem residual : ResidualBound :=
  fun p a b h => GaussianStirlingDuplicationResidual.uniform_sample_bound p a b h

theorem sample_error (p y x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianStirlingIntegerLimit.nameF p y)
      (ap2 GaussianStirlingConstant.nameF p (GaussianStirlingConstant.nameData x)) (num 152) (unit p) :=
  GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (sample_budget_value 64)
    (.eqRefl _) (GaussianStirlingConstantIdentificationCore.sample_error 64 half_step residual p y x)

theorem identification (y x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent GaussianStirlingIntegerLimit.nameF GaussianStirlingConstant.nameF
      y (GaussianStirlingConstant.nameData x) :=
  GaussianStirlingConstantIdentificationCore.identification 64 half_step residual y x

theorem actual_Stirling_integer_limit_equals_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent GaussianStirlingIntegerLimit.nameF GaussianStirlingConstant.nameF
      (var 0) (GaussianStirlingConstant.nameData (var 1))) :=
  closeUniv 2 (identification _ _)

end LeanProofs.IPRA.Analysis.GaussianStirlingConstantIdentification
