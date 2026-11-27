import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.Cofinal.GaussianEulerPowerChartCofinalEndpoints
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartMesh

/-!
# Equal rational inputs to the original power chart

The original normalized chart program is proper across positive rational
encodings. This applies in particular to the actual first and last
physical nodes of the uniform grid for the cofinal cutoff panel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartEquivalentTimes

open_ipra
open GaussianEulerPositivePowerChart (nameF data)
open GaussianEulerPowerChartRationalPowers (chart_proper)
open GaussianEulerPowerChartCofinalEndpoints (source lowerDenominator upperNumerator width)
open GaussianEulerPositivePowerChartMesh (timeNumerator timeDenominator)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gridEndpoints (e f d h S V N : PTm n) : Fm PTm n :=
  let E := lowerDenominator S V f
  let C := width f h S V
  let D := timeDenominator N E
  crossEquivalent nameF constantF (data e f d h S (timeNumerator zero N one C) D)
    (fraction d (h*lowerDenominator S V e)) ⋏
  crossEquivalent nameF constantF (data e f d h S (timeNumerator N N one C) D)
    (fraction (d*upperNumerator h V e) h)

theorem exact_grid_endpoints (e f d h Q S V N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S V) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] gridEndpoints e f d h S V N := by
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  let D := timeDenominator N E
  let a := timeNumerator zero N one C
  let b := timeNumerator N N one C
  let c := fraction d (h*lowerDenominator S V e)
  let v := fraction (d*upperNumerator h V e) h
  have hp := GaussianEulerPowerChartCofinalEndpoints.physical_panel e f d h Q S V hs
  have hE : Γ ⊢[PRAAx] le one E := hp.andE₁
  have hT : Γ ⊢[PRAAx] le one T := hp.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE hN
  have ea : Γ ⊢[PRAAx] a ≐ N := by unfold a timeNumerator; ipra_ring
  have eb : Γ ⊢[PRAAx] b ≐ (T*E)*N :=
    (by unfold b timeNumerator; ipra_ring : Γ ⊢[PRAAx] b ≐ (one+C)*N).eqTrans
      (congrMul hp.andE₂.andE₂.andE₂ (.eqRefl N))
  have ha : Γ ⊢[PRAAx] le one a := le_congr (.eqRefl _) ea.eqSymm hN
  have hb : Γ ⊢[PRAAx] le one b := le_congr (.eqRefl _) eb.eqSymm
    (positive_product _ _ (positive_product _ _ hT hE) hN)
  have el : Γ ⊢[PRAAx] a*E ≐ D*one :=
    (congrMul ea (.eqRefl E)).eqTrans (by unfold D timeDenominator; ipra_ring)
  have er : Γ ⊢[PRAAx] b*one ≐ D*T :=
    (congrMul eb (.eqRefl one)).eqTrans (by unfold D timeDenominator; ipra_ring)
  have left := chart_proper e f d h Q S a D one E hs.andE₁ (.andI ha hD) (.andI (le_refl _) hE) el
  have right := chart_proper e f d h Q S b D T one hs.andE₁ (.andI hb hD) (.andI hT (le_refl _)) er
  have exactEnds := GaussianEulerPowerChartCofinalEndpoints.exact_endpoints e f d h Q S V hs
  exact .andI
    (cross_trans nameF nameF constantF (data e f d h S a D) (data e f d h S one E) c left exactEnds.andE₁)
    (cross_trans nameF nameF constantF (data e f d h S b D) (data e f d h S T one) v right exactEnds.andE₂)

theorem actual_power_chart_cofinal_grid_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      le one (var 7) ⟶ gridEndpoints (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (exact_grid_endpoints _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartEquivalentTimes
