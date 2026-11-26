import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceIntegrandShift
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelWeightedBridgeZero

/-!
# Pointwise Binet Laplace shift with the weighted unit quadrature

The exact unit difference of the original Laplace integrand is the
original complex damping times the checked weighted unit evaluator.
The identity includes the zero-time observation and uses the same
two original cofinal integrand names on the left.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedShiftRow

open_ipra
open GaussianBinetLaplaceIntegrand (input)
open GaussianBinetLaplaceIntegrandShift
  (differenceF differenceData differenceDataWithRadius factoredF factoredData row_factor row_factor_with_radius)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianBinetLaplaceExponential.nameF
local notation "eData" => GaussianBinetLaplaceExponential.data
local notation "Weighted" => GaussianBinetWeightedExponential.nameF
local notation "weightedData" => GaussianBinetWeightedExponential.data

def nameF : PR 2 := multiplyF E Weighted
def data (X Y D sign R T A B : PTm n) : PTm n :=
  multiplyData E Weighted (eData X Y D sign R T A B) (weightedData A B)

ipra_subst data

theorem regular (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign R T A B) :=
  multiply_fast _ _ _ _
    (GaussianBinetLaplaceExponential.regular _ _ _ _ _ _ _ _ h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
    (GaussianBinetKernelWeightedBridgeZero.weighted_regular A B h.andE₂.andE₁)

private theorem factored_weighted (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] crossEquivalent factoredF nameF (factoredData X Y D sign R T A B) (data X Y D sign R T A B) := by
  let x := eData X Y D sign R T A B
  have hb := h.andE₂.andE₁
  have hx := GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ hb h.andE₂.andE₂
  exact multiply_cross E E GaussianBinetKernelWeightedBridge.nameF Weighted x x
    (GaussianBinetKernelWeightedBridge.data A B) (weightedData A B) hx hx
    (GaussianBinetKernelWeightedBridge.regular A B hb) (GaussianBinetKernelWeightedBridgeZero.weighted_regular A B hb)
    (cross_refl _ _ hx) (GaussianBinetKernelWeightedBridgeZero.equivalent A B hb)

theorem original_row (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] crossEquivalent differenceF nameF (differenceData X Y D sign R T A B) (data X Y D sign R T A B) :=
  cross_trans _ _ _ _ _ _ (row_factor X Y D sign R T A B h) (factored_weighted X Y D sign R T A B h)

theorem original_row_with_radius (X Y D sign R S T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) (h' : Γ ⊢[PRAAx] input (X+D) Y D sign S T A B) :
    Γ ⊢[PRAAx] crossEquivalent differenceF nameF (differenceDataWithRadius X Y D sign R S T A B)
      (data X Y D sign R T A B) :=
  cross_trans _ _ _ _ _ _ (row_factor_with_radius X Y D sign R S T A B h h') (factored_weighted X Y D sign R T A B h)

theorem actual_Binet_Laplace_weighted_shift_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let T := var 5
     let A := var 6
     let B := var 7
     input X Y D sign R T A B ⟶ crossEquivalent differenceF nameF
       (differenceData X Y D sign R T A B) (data X Y D sign R T A B)) :=
  closeUniv 8 (.impI (original_row _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_Binet_Laplace_weighted_shift_row_with_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let S := var 5
     let T := var 6
     let A := var 7
     let B := var 8
     (input X Y D sign R T A B ⋏ input (X+D) Y D sign S T A B) ⟶
       crossEquivalent differenceF nameF (differenceDataWithRadius X Y D sign R S T A B)
         (data X Y D sign R T A B)) :=
  closeUniv 9 (.impI (original_row_with_radius _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedShiftRow
