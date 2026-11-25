import IPRADerivations.Analysis.GaussianStirlingLogDuplication

/-!
# Invariance under positive rescaling of the rational log-Gamma input

The native Gamma names already agree after a common positive scaling
of numerator and denominator. Exponential recovery and injectivity
on the real axis give the same invariance for the actual log-Gamma
names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaLogRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalHorner (positive_product)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular log_gamma_axis)
open GaussianStirlingLogDuplication (exponential_gamma)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem log_gamma_rescale (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF logGammaF (logGammaData (k*a) (k*b)) (logGammaData a b) := by
  let x := logGammaData (k*a) (k*b)
  let y := logGammaData a b
  have scaled : Γ ⊢[PRAAx] source (k*a) (k*b) :=
    .andI (positive_product _ _ hk hs.andE₁) (positive_product _ _ hk hs.andE₂)
  have rx := log_gamma_regular (k*a) (k*b) scaled
  have ry := log_gamma_regular a b hs
  apply independent_radii_injective logGammaF logGammaF (U logGammaF x) (U logGammaF y) x y
    (exponential_input logGammaF x rx) (exponential_input logGammaF y ry)
    (log_gamma_axis (k*a) (k*b)) (log_gamma_axis a b)
  exact cross_trans _ _ _ _ _ _ (exponential_gamma (k*a) (k*b) scaled)
    (cross_trans _ _ _ _ _ _ (GaussianStirlingNativeDuplication.gamma_rescale a b k hs hk)
      (cross_symm _ _ _ _ (exponential_gamma a b hs)))

theorem actual_positive_rational_log_Gamma_rescale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le one (var 2) ⟶ crossEquivalent logGammaF logGammaF
      (logGammaData (var 2*var 0) (var 2*var 1)) (logGammaData (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (log_gamma_rescale _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaLogRescale
