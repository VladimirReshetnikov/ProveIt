import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumFreeze
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaPositiveRationalProperness
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaLocationInput

/-!
# Freeze log Gamma at the original dyadic critical location

The frozen native datum uses the selected grid numerator and denominator
directly. It therefore agrees with the datum used by the native critical
point estimates, independently of the decoder's fraction reduction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreezeLocation

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaDigammaDyadicLocation (locationF lower)
open GaussianGammaDigammaDyadicMesh (grid)
open GaussianGammaDigammaLocationInput (named_source named_real_source frozen_fraction_at rational_source)
open GaussianGammaMinimumFreeze (nameF data frozen_log_rate_at_rational)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData gammaLogMargin)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "modulus" => GaussianGammaHalfPlaneInputContinuity.modulus

theorem frozen_root_log_rate (s r x : PTm n) (hl : Γ ⊢[PRAAx] le (threshold one) r)
    (hd : Γ ⊢[PRAAx] le (succ (modulus s (radius locationF x) (two*one))) r) :
    Γ ⊢[PRAAx] independentRate (nameF locationF) logGammaF (data x one)
      (logGammaData (lower r) (grid r)) gammaLogMargin (unit s) := by
  have hi : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input locationF s r x one :=
    .andI (named_source x) (.andI hl hd)
  have cross := GaussianGammaPositiveRationalProperness.original_cross _ _ _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source locationF s r x one hi) (rational_source r)
    (frozen_fraction_at r x)
  exact frozen_log_rate_at_rational locationF s r x one (lower r) (grid r) (named_real_source x) hi
    (rational_source r) cross

theorem computed_root_log_rate (s x : PTm n) :
    Γ ⊢[PRAAx] independentRate (nameF locationF) logGammaF (data x one)
      (logGammaData (lower (GaussianNamedGammaPositiveLower.clock locationF s x one))
        (grid (GaussianNamedGammaPositiveLower.clock locationF s x one))) gammaLogMargin (unit s) :=
  frozen_root_log_rate s _ x (le_add_right _ _) (le_add_left _ _)

theorem actual_original_log_Gamma_at_frozen_dyadic_location_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (independentRate (nameF locationF) logGammaF (data (var 1) one)
        (logGammaData (lower (GaussianNamedGammaPositiveLower.clock locationF (var 0) (var 1) one))
          (grid (GaussianNamedGammaPositiveLower.clock locationF (var 0) (var 1) one)))
          gammaLogMargin (unit (var 0))) :=
  closeUniv 2 (computed_root_log_rate _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreezeLocation
