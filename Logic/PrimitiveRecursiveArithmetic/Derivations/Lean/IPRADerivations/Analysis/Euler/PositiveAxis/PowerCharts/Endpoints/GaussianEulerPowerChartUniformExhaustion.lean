import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartUniformSchedule

/-!
# Cofinality of the uniform physical panels

The same panel used by the uniform comparison eventually contains
every fixed interval with positive rational endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformExhaustion

open_ipra
open GaussianEulerPowerChartUniformSchedule (cutoffIndex panelStage)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize cutoff_guards)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianGammaIntegralCutoffs (top height tailCoefficient)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem power_later (S V L : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (hV : Γ ⊢[PRAAx] le one V) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] le V (pw (S*V) L) := by
  have base : Γ ⊢[PRAAx] le V (S*V) := le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hS)
  exact le_trans base (le_congr (pw_one _) (.eqRefl _)
    (GaussianFactorBudget.power_monotone_length (S*V) one L (le_trans hV base) hL))

def contains (s A R L M S U a b c d : PTm n) : Fm PTm n :=
  let V := cutoffSize (cutoffIndex s A R L M) A R
  le b (a*lowerDenominator S V L) ⋏ le c (d*upperNumerator U V L)

theorem endpoints_later (s A R L M S U : PTm n)
    (hL : Γ ⊢[PRAAx] le one L) (hS : Γ ⊢[PRAAx] le one S)
    (hU : Γ ⊢[PRAAx] le one U) :
    let V := cutoffSize (cutoffIndex s A R L M) A R
    Γ ⊢[PRAAx] le s (lowerDenominator S V L) ⋏ le s (upperNumerator U V L) := by
  dsimp only
  let j := cutoffIndex s A R L M
  let V := cutoffSize j A R
  have hStage : Γ ⊢[PRAAx] le s (panelStage s L) :=
    le_trans (le_add_right s (num 3)) (le_add_right _ _)
  have hIndex : Γ ⊢[PRAAx] le s j :=
    le_trans hStage (le_trans (le_add_right _ two) (le_trans (le_succ_self _) (le_add_right _ _)))
  have hTop : Γ ⊢[PRAAx] le j (top j A R) := by
    unfold top height
    ipra_le 𝔞 j+2*𝔞 A+2*𝔞(tailCoefficient R)+20
  have guard := cutoff_guards (Γ := Γ) j A R
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) guard.andE₁
  have later : Γ ⊢[PRAAx] le s V :=
    le_trans hIndex (le_trans hTop (le_trans (le_add_right _ _) guard.andE₂.andE₂))
  exact .andI (le_trans later (power_later S V L hS hV hL))
    (le_trans later (power_later U V L hU hV hL))

theorem original_panel_contains (s A R L M S U a b c d : PTm n)
    (hL : Γ ⊢[PRAAx] le one L) (hS : Γ ⊢[PRAAx] le one S) (hU : Γ ⊢[PRAAx] le one U)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d)
    (hb : Γ ⊢[PRAAx] le b s) (hc : Γ ⊢[PRAAx] le c s) :
    Γ ⊢[PRAAx] contains s A R L M S U a b c d := by
  let V := cutoffSize (cutoffIndex s A R L M) A R
  let E := lowerDenominator S V L
  let T := upperNumerator U V L
  have ends := endpoints_later s A R L M S U hL hS hU
  exact .andI (le_trans (le_trans hb ends.andE₁)
    (le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E ha)))
    (le_trans (le_trans hc ends.andE₂)
      (le_congr (one_mul T) (.eqRefl _) (mul_le_mul_right T hd)))

theorem actual_uniform_power_damped_source_panels_exhaust_positive_times_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      ((((le one (var 3) ⋏ le one (var 5)) ⋏ le one (var 6)) ⋏
        ((le one (var 7) ⋏ le one (var 10)) ⋏
          (le (var 8) (var 0) ⋏ le (var 9) (var 0)))) ⟶
        contains (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) :=
  closeUniv 11 (.impI (original_panel_contains _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁.andE₁ Prf.hyp0.andE₁.andE₁.andE₂ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformExhaustion
