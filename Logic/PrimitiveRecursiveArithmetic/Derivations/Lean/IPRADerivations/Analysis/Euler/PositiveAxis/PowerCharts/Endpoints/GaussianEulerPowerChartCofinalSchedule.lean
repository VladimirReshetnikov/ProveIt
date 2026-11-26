import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartRoundedEndpoints
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingGridSchedule
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustion

/-!
# Cofinal corrected image panels for the original substitution schedule

The size V is chosen from the exact target cutoff. The precision s+2V
allows both endpoint errors on the grid used by finite substitution.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartCofinalSchedule

open_ipra
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianEulerPowerChartRoundedEndpoints (chartBudget original_rounded_panel_contains)
open GaussianEulerPowerScalingGridSchedule (count imagePrecision)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPositivePowerChartCorrectedPanel (start span denominator)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPowerScalingCell (scaleBound eulerBound)
open GaussianEulerPowerScalingFrozenIntegrand (factorBound)
open GaussianEulerPowerChartFrozenKernel (cost)
open GaussianEulerPowerScalingCorrectedQuadrature (gain)
open GaussianEulerPowerScalingFiniteBudget (chartCost)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def cutoffSize (j A R : PTm n) : PTm n := two*(etaDen j A R+top j A R+one)
def samplingIndex (s V : PTm n) : PTm n := s+two*V
def source (z R B A e f d h L Q S : PTm n) : Fm PTm n :=
  GaussianEulerPowerScalingParameter.source z R B A e f L Q ⋏
    GaussianEulerPositivePowerChart.parameters e f d h Q S

theorem cutoff_guards (j A R : PTm n) : Γ ⊢[PRAAx]
    le two (cutoffSize j A R) ⋏
      (le (two*etaDen j A R) (cutoffSize j A R) ⋏ le (top j A R+one) (cutoffSize j A R)) := by
  unfold cutoffSize
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_le 𝔞(two*etaDen j A R)+𝔞(two*top j A R)
  · ipra_le 𝔞(two*top j A R)+2
  · ipra_le 𝔞(two*etaDen j A R)+𝔞(top j A R)+1

theorem count_positive (s z R B e f d h L Q S E T C : PTm n) :
    Γ ⊢[PRAAx] le one (count s z R B e f d h L Q S E T C) :=
  le_trans (GaussianEulerPowerScalingGridSchedule.mesh_factor_positive _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (GaussianEulerPowerScalingGridSchedule.mesh_factor_le_count _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem chart_clock_budget (s z R B e f d h L Q S E T C N V : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le (chartBudget N V)
      (unit (query (imagePrecision (samplingIndex s V) z R B e f d h L Q S E T C N) h Q E T)) := by
  let t := samplingIndex s V
  let K := chartCost N Q C (factorBound z B e f d h E*cost (L*R) h Q S E T)
    (scaleBound z B e f d h) (eulerBound (L*R) h Q S E T)
    (GaussianEulerPositivePowerChart.lipschitz Q S E T) (gain (L*R) h Q S E T N)
  let p := imagePrecision t z R B e f d h L Q S E T C N
  have unitBound : Γ ⊢[PRAAx] le (two*V) (unit t) :=
    le_trans (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self _)
      (GaussianExponentialReference.unit_monotone (le_add_left _ _))
  have goal : Γ ⊢[PRAAx] le (chartBudget N V) ((num 3*K+two*N)*unit t) := by
    unfold chartBudget
    ipra_le 𝔞(two*V)*sl hN+𝔞(two*N)*sl unitBound+𝔞(num 3*K*unit t)
  have initial : Γ ⊢[PRAAx] le ((num 3*K+two*N)*unit t) (unit p) :=
    GaussianFastValueCut.query_budget _ _
  exact le_trans (le_trans goal initial) (GaussianExponentialReference.unit_monotone
    (GaussianEulerPositivePowerChartImage.query_later p h Q E T))

def imageSource (j s z R B A e f d h L Q S : PTm n) : Fm PTm n :=
  let R' := L*R
  let B' := B*e
  let A' := Q*A
  let V := cutoffSize j A' R'
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  let t := samplingIndex s V
  let N := count t z R B e f d h L Q S E T C
  let k := imagePrecision t z R B e f d h L Q S E T C N
  GaussianEulerCompactExhaustion.source (scaled z f) R' B' A' j
    (start k e f d h Q S E T one C N) (span k e f d h Q S E T one C N)
    (denominator k e f d h Q S E T one C N) (reciprocalMargin h Q E T)
    (GaussianEulerPositivePowerChart.majorant Q S E T+one)

theorem original_scheduled_image_source (j s z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) : Γ ⊢[PRAAx] imageSource j s z R B A e f d h L Q S := by
  let R' := L*R
  let B' := B*e
  let A' := Q*A
  let V := cutoffSize j A' R'
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  let t := samplingIndex s V
  let N := count t z R B e f d h L Q S E T C
  let k := imagePrecision t z R B e f d h L Q S E T C N
  have target := GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hs.andE₁
  have guards := cutoff_guards (Γ := Γ) j A' R'
  have physical : Γ ⊢[PRAAx] GaussianEulerPowerChartCofinalEndpoints.source e f d h Q S V :=
    .andI hs.andE₂ guards.andE₁
  have panel := GaussianEulerPowerChartCofinalEndpoints.physical_panel e f d h Q S V physical
  have hN : Γ ⊢[PRAAx] le one N := count_positive t z R B e f d h L Q S E T C
  have hk : Γ ⊢[PRAAx] le (chartBudget N V) (unit (query k h Q E T)) :=
    chart_clock_budget s z R B e f d h L Q S E T C N V hN
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) guards.andE₁
  have small : Γ ⊢[PRAAx] le (two*N) (unit (query k h Q E T)) := by
    apply le_trans _ hk
    unfold chartBudget
    ipra_le 𝔞(two*N)*sl hV+𝔞(two*V)
  have mesh : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T one C N :=
    .andI hs.andE₂ (.andI panel.andE₁ (.andI (le_refl _)
      (.andI (le_congr panel.andE₂.andE₂.andE₂.eqSymm (.eqRefl _) (le_refl (T*E))) hN)))
  have geometry := GaussianEulerPositivePowerChartCorrectedPanel.panel_geometry k e f d h Q S E T one C N (.andI mesh small)
  have contains := original_rounded_panel_contains k e f d h Q S V N (etaDen j A' R') (top j A' R')
    physical hN guards.andE₂.andE₁ guards.andE₂.andE₂ hk
  have margin := GaussianEulerPositivePowerChartImage.margin_positive h Q E T hs.andE₂.andE₂.andE₁.andE₂
  exact .andI target (.andI (.andI (.andI target.andE₁.andE₂.andE₁.andE₁
    (.andI margin target.andE₁.andE₂.andE₁.andE₂)) geometry) contains)

theorem actual_original_scheduled_power_chart_exhaustion_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      imageSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)) :=
  closeUniv 13 (.impI (original_scheduled_image_source _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartCofinalSchedule
