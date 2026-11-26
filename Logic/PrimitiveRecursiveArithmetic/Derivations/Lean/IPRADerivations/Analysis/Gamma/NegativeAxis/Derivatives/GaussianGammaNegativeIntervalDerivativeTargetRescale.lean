import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalDerivativeTarget
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalRescale
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalRescale

/-!
# The original derivative target at a common rational denominator

Both the original Gamma and the literal shifted digamma preserve their
values when the rational offset is encoded by a positive rescaling.
Their named product therefore preserves the derivative residual.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDerivativeTargetRescale

open_ipra
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalDerivativeTarget (nameF data)
open GaussianGammaNegativeIntervalNative (negative_regular)
open GaussianGammaNegativeIntervalRescale (guard_rescale)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_rescale (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (D*a) (D*b) N) (data a b N) := by
  let S := GaussianGammaNegativeCriticalEndpoints.nameF
  let gd := GaussianGammaNegativeIntervalNative.data (n := n)
  let sd := GaussianGammaNegativeCriticalEndpoints.nameData (n := n)
  have scaled := guard_rescale a b D h hD
  exact GaussianGammaAdjacentCutoff.multiply_cross gammaF gammaF S S (gd (D*a) (D*b) N) (gd a b N)
    (sd (D*a) (D*b) N) (sd a b N) (negative_regular _ _ _ scaled) (negative_regular _ _ _ h)
    (GaussianGammaNegativeCriticalEndpoints.name_regular _ _ _ scaled) (GaussianGammaNegativeCriticalEndpoints.name_regular _ _ _ h)
    (GaussianGammaNegativeIntervalRescale.original_rescale a b D N h hD)
    (GaussianGammaNegativeCriticalRescale.original_rescale a b N D h hD)

theorem actual_original_negative_Gamma_derivative_target_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ le one (var 3)) ⟶
        crossEquivalent nameF nameF (data (var 3*var 0) (var 3*var 1) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (original_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDerivativeTargetRescale
