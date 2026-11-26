import IPRADerivations.Analysis.Gamma.Names.Continuation.GaussianNamedGammaBackwardFrozen
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaNativeShiftRecurrence
import IPRADerivations.Analysis.Gamma.Names.Continuation.GaussianGammaNativeBackwardGuard

/-!
# The backward name represents the original pole-free Gamma

The independent-observation estimate compares the named backward shift
with the unchanged original Gamma at each sufficiently late exact native
sample. The numerical guard excludes the zero pole using apartness and
the other poles using the positive margin at the shifted argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaBackwardIdentification

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedGammaBackwardShift (source nameF data name_regular)
open GaussianNamedGammaBackwardFrozen (nativeW nativeZ nativeDen freezeClock accuracy positive_late_input late_anchor)
open GaussianNamedRightHalfPlane (radius)
open GaussianNameReciprocal (R R_positive)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNamedInverseRate (independentRate)
open GaussianNameEquivalence (cross_refl)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def encodedData (f : PR 2) (k x A a : PTm n) : PTm n :=
  gammaData (nativeW f k x) (radius f x+one) (nativeDen f k x) ((two*A)*R a)

theorem original_native_backward_source (f : PR 2) (s k x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a) (hk : Γ ⊢[PRAAx] le (freezeClock f s x A a) k) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (nativeW f k x) (radius f x+one)
      (nativeDen f k x) one ((two*A)*R a) := by
  have hp := positive_late_input f s k x A a hs hk
  have hz := GaussianNamedGammaLateInput.encoded_source f _ _ _ _ hp
  have hw := GaussianNamedGammaBackwardFrozen.original_native_lower f k x A a hs (late_anchor f s k x A a hk)
  exact GaussianGammaNativeBackwardGuard.backward_source _ _ _ _ _ hz (R_positive a) hw

theorem original_independent_rate (f : PR 2) (s k x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a) (hk : Γ ⊢[PRAAx] le (freezeClock f s x A a) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) gammaF (data f x A a) (encodedData f k x A a) one (unit s) := by
  let w := nativeW f k x
  let z := nativeZ f k x
  let B := nativeDen f k x
  let S := radius f x
  let D := (two*A)*R a
  let Y := GaussianNamedGammaBackwardFrozen.frozenF
  let y := GaussianNamedGammaBackwardFrozen.frozenData f k x A
  have hw := original_native_backward_source f s k x A a hs hk
  have hz := GaussianNamedGammaLateInput.encoded_source f _ _ _ _ (positive_late_input f s k x A a hs hk)
  have positive := GaussianGammaHalfPlaneInputContinuity.reciprocal_source z S B (two*A) hz
  have proper := GaussianGammaNativeShiftRecurrence.original_gamma_shift_inverse w z (S+one) S B one D one (two*A)
    hw positive (GaussianGammaNativeBackwardGuard.shifted_back z B)
  have r := GaussianNamedGammaBackwardFrozen.original_positive_quotient_rate f s k x A a hs hk
  exact GaussianNamedRateTransport.transport (nameF f) Y (nameF f) gammaF (data f x A a) y (data f x A a)
    (encodedData f k x A a) one (unit s) (unit_positive s) r
    (cross_refl _ _ (name_regular f x A a hs)) proper

theorem actual_original_named_backward_Gamma_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source f (var 2) (var 3) (var 4) ⋏ le (freezeClock f (var 0) (var 2) (var 3) (var 4)) (var 1)) ⟶
        independentRate (nameF f) gammaF (data f (var 2) (var 3) (var 4))
          (encodedData f (var 1) (var 2) (var 3) (var 4)) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_independent_rate f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaBackwardIdentification
