import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentZeroOrder
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFirstFormula

/-!
# The zeroth actual Binet moment is the original real Stirling remainder

Bind the unweighted improper Binet name from first Binet to the exact
zero-order member of the actual moment family.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentStirling

open_ipra
open GaussianBinetLaplaceMomentZeroOrder (improper_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "UJ" => GaussianBinetLaplaceImproperName.nameF
local notation "UD" => GaussianBinetLaplaceImproperName.data
local notation "MJ" => GaussianBinetLaplaceMomentImproper.nameF
local notation "MD" => GaussianBinetLaplaceMomentImproper.data

theorem stirling_equivalent (X D x : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D zero) :
    Γ ⊢[PRAAx] crossEquivalent GaussianStirlingGlobalBounds.remainderF MJ
      (GaussianStirlingGlobalBounds.remainderData X D x)
      (MD zero X D (GaussianLogGammaEulerResidualRadius.radius X zero)) := by
  let F := GaussianBinetStirlingRemainder.nameF
  let d := GaussianBinetStirlingRemainder.data X zero D zero x
  let R := GaussianLogGammaEulerResidualRadius.radius X zero
  have rh := GaussianLogGammaEulerResidualRadius.source_of_right_half_plane X zero D zero h
  have a := GaussianBinetStirlingRemainder.axis_equivalent X D zero x h
  have b := GaussianBinetFirstFormula.equivalent X zero D zero x h
  have c := improper_equivalent X D R rh
  exact cross_trans _ F _ _ d _
    (cross_symm _ _ _ _ a) (cross_trans _ UJ _ _ (UD X zero D zero R) _ b (cross_symm _ _ _ _ c))

theorem actual_zeroth_Binet_moment_original_Stirling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRightHalfPlaneLogarithm.source (var 0) (var 1) zero ⟶
      crossEquivalent GaussianStirlingGlobalBounds.remainderF MJ
        (GaussianStirlingGlobalBounds.remainderData (var 0) (var 1) (var 2))
        (MD zero (var 0) (var 1) (GaussianLogGammaEulerResidualRadius.radius (var 0) zero))) :=
  closeUniv 3 (.impI (stirling_equivalent _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentStirling
