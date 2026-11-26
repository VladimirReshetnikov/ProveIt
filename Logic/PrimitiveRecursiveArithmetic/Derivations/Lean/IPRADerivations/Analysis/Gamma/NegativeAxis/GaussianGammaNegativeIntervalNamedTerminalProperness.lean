import IPRADerivations.Analysis.Euler.Logarithms.GaussianNamedEulerLogarithmicParameterRate
import IPRADerivations.Analysis.Euler.Logarithms.GaussianNamedEulerLogarithmicZeroIdentification
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Equivalent terminal inputs give equivalent original Euler names

The arbitrary-parameter rate specializes to cross-equivalent input
names at every precision. Removing its bounded auxiliary dyadic
error identifies Euler integral names at different certified margins.
The order-zero identification transports this to original named Gamma.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedDifferenceRate (self_rate)
open GaussianNamedInverseRate (independentRate denominator_positive rateNumerator rateDenominator)
open GaussianNamedRightHalfPlane (source)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ld" => GaussianNamedEulerLogarithmicImproper.data
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data

private theorem input_rate (f g : PR 2) (x y D : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] independentRate f g x y one D := by
  have same := GaussianNamedRateTransport.transport f f f g x x x y zero one (le_refl one)
    (self_rate f x hf) (cross_refl _ _ hf) (cross_symm _ _ _ _ he)
  exact GaussianNamedRateRadius.weaken f g x y zero one one D (le_refl one) hD (by ipra_le 1) same

private theorem euler_diagonal (f g : PR 2) (p j x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A) (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (L f) p (ld j x A)) (ap2 (L g) p (ld j y B)) (num 7) (unit p) := by
  let D := two*GaussianNamedEulerLogarithmicParameterRate.inputRadius g p j y B
  have hM : Γ ⊢[PRAAx] le one (GaussianNamedEulerLogarithmicParameterRate.inputRadius g p j y B) :=
    GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ RationalAlgebra.two_positive hM
  have hs : Γ ⊢[PRAAx] GaussianNamedEulerLogarithmicParameterRate.source g f p j y x B A :=
    .andI hg (.andI hf (input_rate f g x y D hf.andE₁ hD he))
  have close := GaussianNamedEulerLogarithmicParameterRate.original_observations g f p p p j y x B A hs
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive (unit p) p p hp) hp
    (by unfold rateNumerator rateDenominator; ipra_le 0) close

theorem original_euler_proper (f g : PR 2) (j x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A) (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (L f) (L g) (ld j x A) (ld j y B) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 7)
    (GaussianNamedEulerLogarithmicImproper.name_regular f j x A hf)
    (GaussianNamedEulerLogarithmicImproper.name_regular g j y B hg) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have fs : Δ ⊢[PRAAx] source f (sh x) (sh A) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift
  have gs : Δ ⊢[PRAAx] source g (sh y) (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift
  have es : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNamedEulerLogarithmicImproper.subst_data,
    PTm.subst_num,Syn.shift,sh] using euler_diagonal f g (var 0) (sh j) (sh x) (sh y) (sh A) (sh B) fs gs es

theorem original_gamma_proper (f g : PR 2) (x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A) (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (G f) (G g) (gd x A) (gd y B) :=
  cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (GaussianNamedEulerLogarithmicZeroIdentification.original_order_zero_is_Gamma f x A hf))
    (cross_trans _ _ _ _ _ _ (original_euler_proper f g zero x y A B hf hg he)
      (GaussianNamedEulerLogarithmicZeroIdentification.original_order_zero_is_Gamma g y B hg))

theorem actual_original_named_half_plane_Gamma_proper_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 3)) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (G f) (G g) (gd (var 0) (var 2)) (gd (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_gamma_proper f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalDerivative
