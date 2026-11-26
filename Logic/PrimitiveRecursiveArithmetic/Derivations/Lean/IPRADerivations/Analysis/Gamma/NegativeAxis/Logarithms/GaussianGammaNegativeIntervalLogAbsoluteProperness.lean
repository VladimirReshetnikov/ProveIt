import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalLogAbsolute
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalRescale

/-!
# Rescaling the rational input of log-absolute Gamma

The original Gamma rescaling and the fixed sign on the interval give
equal exponentials. Real injectivity then gives the same log-absolute
name at the two numerator-denominator representations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsoluteProperness

open_ipra
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData name_regular name_axis original_exponential)
open GaussianGammaNegativeIntervalNative (data negative_regular)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaNegativeIntervalRescale (guard_rescale original_rescale)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem signed_rescale (a b D N : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent signedF signedF (signedData (D*a) (D*b) N) (signedData a b N) :=
  multiply_cross constantF constantF gammaF gammaF (signUnit (succ N)) (signUnit (succ N))
    (data (D*a) (D*b) N) (data a b N) (constant_regular _) (constant_regular _)
    (negative_regular (D*a) (D*b) N (guard_rescale a b D h hD)) (negative_regular a b N h)
    (cross_refl _ _ (constant_regular _)) (original_rescale a b D N h hD)

theorem log_absolute_rescale (a b D N : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (nameData (D*a) (D*b) N) (nameData a b N) := by
  let x := nameData (D*a) (D*b) N
  let y := nameData a b N
  have hs := guard_rescale a b D h hD
  apply independent_radii_injective nameF nameF (U nameF x) (U nameF y) x y
    (exponential_input _ _ (name_regular (D*a) (D*b) N hs)) (exponential_input _ _ (name_regular a b N h))
    (name_axis (D*a) (D*b) N) (name_axis a b N)
  exact cross_trans _ _ _ _ _ _ (original_exponential (D*a) (D*b) N hs)
    (cross_trans _ _ _ _ _ _ (signed_rescale a b D N h hD)
      (cross_symm _ _ _ _ (original_exponential a b N h)))

theorem actual_original_negative_interval_log_absolute_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (guard (var 0) (var 1) ⟶ le one (var 2) ⟶ crossEquivalent nameF nameF
        (nameData (var 2*var 0) (var 2*var 1) (var 3)) (nameData (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (log_absolute_rescale _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsoluteProperness
