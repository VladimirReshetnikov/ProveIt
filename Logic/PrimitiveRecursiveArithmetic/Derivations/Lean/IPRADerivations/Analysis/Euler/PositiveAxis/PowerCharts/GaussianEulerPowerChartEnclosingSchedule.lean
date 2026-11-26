import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartEnclosingOrders
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartUniformSchedule

/-!
# Scheduled corrected images for arbitrary enclosing physical panels

The uniform schedule supplies the required physical interval.
Every enclosing positive rational panel can use its own mesh clocks
while still enclosing the original Euler cutoff after substitution.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartEnclosingSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerChartEnclosingOrders (contains enclosing_grid_orders)
open GaussianEulerPowerChartUniformEndpoints (uniform_reference_bounds)
open GaussianEulerPowerChartUniformRounded (rounded_panel_of_orders)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize samplingIndex cutoff_guards chart_clock_budget count_positive)
open GaussianEulerPowerChartRoundedEndpoints (chartBudget)
open GaussianEulerPowerScalingGridSchedule (source count imagePrecision)
open GaussianEulerPositivePowerChartCorrectedPanel (start span denominator)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def imageSource (j s z R B A e f d h L Q S E T a W : PTm n) : Fm PTm n :=
  let R' := L*R
  let A' := Q*A
  let V := cutoffSize j A' R'
  let t := samplingIndex s V
  let N := count t z R B e f d h L Q S E T W
  let k := imagePrecision t z R B e f d h L Q S E T W N
  GaussianEulerCompactExhaustion.source (scaled z f) R' (B*e) A' j
    (start k e f d h Q S E T a W N) (span k e f d h Q S E T a W N)
    (denominator k e f d h Q S E T a W N) (reciprocalMargin h Q E T)
    (GaussianEulerPositivePowerChart.majorant Q S E T+one)

theorem original_enclosing_image_source (j s z R B A e f d h L Q S U E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W)
    (hU : Γ ⊢[PRAAx] le one U) (hu : Γ ⊢[PRAAx] le h (d*U))
    (hleft : Γ ⊢[PRAAx] le (a*lowerDenominator S (cutoffSize j (Q*A) (L*R)) L) E)
    (hright : Γ ⊢[PRAAx] le (E*upperNumerator U (cutoffSize j (Q*A) (L*R)) L) (a+W)) :
    Γ ⊢[PRAAx] imageSource j s z R B A e f d h L Q S E T a W := by
  let R' := L*R
  let A' := Q*A
  let V := cutoffSize j A' R'
  let t := samplingIndex s V
  let N := count t z R B e f d h L Q S E T W
  let k := imagePrecision t z R B e f d h L Q S E T W N
  have params := hs.andE₂.andE₁
  have target := GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hs.andE₁
  have guards := cutoff_guards (Γ := Γ) j A' R'
  have inverse := le_congr (.eqRefl _) (mul_comm L e) hs.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have physical : Γ ⊢[PRAAx] GaussianEulerPowerChartUniformEndpoints.source e f d h Q S L U V :=
    .andI params (.andI (.andI hs.andE₁.andE₂.andE₂.andE₂.andE₁ hU)
      (.andI (.andI inverse hu) guards.andE₁))
  have hN : Γ ⊢[PRAAx] le one N := count_positive t z R B e f d h L Q S E T W
  have hk : Γ ⊢[PRAAx] le (chartBudget N V) (unit (query k h Q E T)) :=
    chart_clock_budget s z R B e f d h L Q S E T W N V hN
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) guards.andE₁
  have small : Γ ⊢[PRAAx] le (two*N) (unit (query k h Q E T)) := by
    apply le_trans _ hk
    unfold chartBudget
    ipra_le 𝔞(two*N)*sl hV+𝔞(two*V)
  have mesh : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T a W N :=
    .andI params (.andI hs.andE₂.andE₂.andE₁
      (.andI hs.andE₂.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₂.andE₂ hN)))
  have geometry := GaussianEulerPositivePowerChartCorrectedPanel.panel_geometry k e f d h Q S E T a W N (.andI mesh small)
  have orders := enclosing_grid_orders e f d h Q S L U V E T a W N physical mesh (.andI hleft hright)
  have bounds := uniform_reference_bounds d h S U V params.andE₂.andE₂.andE₂.andE₂ hu
  have contains := rounded_panel_of_orders k e f d h Q S U V E T a W N (etaDen j A' R') (top j A' R')
    mesh hV bounds.andE₁ bounds.andE₂ orders.andE₁ orders.andE₂ guards.andE₂.andE₁ guards.andE₂.andE₂ hk
  have margin := GaussianEulerPositivePowerChartImage.margin_positive h Q E T params.andE₂.andE₁.andE₂
  exact .andI target (.andI (.andI (.andI target.andE₁.andE₂.andE₁.andE₁
    (.andI margin target.andE₁.andE₂.andE₁.andE₂)) geometry) contains)

theorem actual_original_enclosing_power_chart_image_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)
        (var 14) (var 15) (var 16) (var 17) ⋏ (le one (var 13) ⋏ le (var 9) (var 8*var 13))) ⋏
      contains (var 10) (var 13) (var 12) (cutoffSize (var 0) (var 11*var 5) (var 10*var 3))
        (var 16) (var 17) (var 14) ⟶
      imageSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
        (var 9) (var 10) (var 11) (var 12) (var 14) (var 15) (var 16) (var 17)) :=
  closeUniv 18 (.impI (original_enclosing_image_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartEnclosingSchedule
