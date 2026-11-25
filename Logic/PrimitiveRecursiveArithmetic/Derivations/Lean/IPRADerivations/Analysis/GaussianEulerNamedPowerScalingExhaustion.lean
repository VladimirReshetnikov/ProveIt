import IPRADerivations.Analysis.GaussianEulerNamedPowerScalingImproper
import IPRADerivations.Analysis.GaussianEulerPowerChartUniformExhaustion

/-!
# Cofinality of the actual named power-damped Euler panels

The literal physical panels used by the named sampler eventually
contain every fixed interval with positive rational endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingExhaustion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerNamedPowerScalingFormula (source)
open GaussianEulerNamedPowerScalingImproper (nameF data scaleBound)
open GaussianEulerNamedPowerScalingCutoff (outputPrecision panelSize)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianNamedPositiveLogarithm (denominator decoded_domain)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def selectedSize (F G : PR 2) (p z R B A x E y H J : PTm n) : PTm n :=
  panelSize (outputPrecision p) R A H J (scaleBound F G z R B x E y H)

def contains (F G : PR 2) (p z R B A x E T y H J a b c d : PTm n) : Fm PTm n :=
  let V := selectedSize F G p z R B A x E y H J
  le b (a*lowerDenominator T V H) ⋏ le c (d*upperNumerator E V H)

/-- The compact sample uses the physical lower endpoint 1/D and upper endpoint U. -/
theorem original_at_selected_panel (F G : PR 2) (p z R B A x E T y H J : PTm n) :
    let V := selectedSize F G p z R B A x E y H J
    Γ ⊢[PRAAx] ap2 (nameF F G) p (data F G z R B A x E T y H J) ≐
      ap2 (GaussianNamedDampingPowerCompact.nameF F G) (outputPrecision p)
        (GaussianNamedDampingPowerCompact.data z R B x y T J one (width H E T V)
          (lowerDenominator T V H) (upperNumerator E V H)) :=
  GaussianEulerNamedPowerScalingCutoff.name_at F G p z R B A x E T y H J (scaleBound F G z R B x E y H)

theorem original_panel_contains (F G : PR 2) (p z R B A x E T y H J a b c d : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d)
    (hb : Γ ⊢[PRAAx] le b p) (hc : Γ ⊢[PRAAx] le c p) :
    Γ ⊢[PRAAx] contains F G p z R B A x E T y H J a b c d := by
  have cc := decoded_domain F zero x E T hs.andE₂
  have hT := GaussianDominantScalarOrder.factor_positive_left T (denominator F zero x)
    (le_trans cc.andE₁.andE₁ cc.andE₂.andE₂)
  have hp : Γ ⊢[PRAAx] le p (outputPrecision p) := le_add_right _ _
  exact GaussianEulerPowerChartUniformExhaustion.original_panel_contains (outputPrecision p) (J*A) (H*R) H
    (scaleBound F G z R B x E y H) T E a b c d hs.andE₁.andE₂.andE₂.andE₂.andE₁ hT hs.andE₂.andE₂.andE₁
    ha hd (le_trans hb hp) (le_trans hc hp)

theorem actual_original_named_power_damped_Euler_panels_exhaust_positive_times_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
      ((source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⋏
        ((le one (var 11) ⋏ le one (var 14)) ⋏ (le (var 12) (var 0) ⋏ le (var 13) (var 0)))) ⟶
        contains F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
          (var 10) (var 11) (var 12) (var 13) (var 14)) :=
  closeUniv 15 (.impI (original_panel_contains F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingExhaustion
