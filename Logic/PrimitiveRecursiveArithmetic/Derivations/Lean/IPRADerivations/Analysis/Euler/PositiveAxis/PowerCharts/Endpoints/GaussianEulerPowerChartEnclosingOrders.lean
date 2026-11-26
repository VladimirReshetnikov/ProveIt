import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartTimeOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartUniformRounded

/-!
# Orders at the exact grid endpoints of any enclosing physical panel

The original chart at the first and last grid times is compared to
the chart at the two fixed physical cutoffs. No shared denominator
is needed between the arbitrary panel and the fixed cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartEnclosingOrders

open_ipra
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianEulerPowerChartUniformEndpoints (uniform_physical_panel uniform_endpoint_order)
open GaussianEulerPositivePowerChart (nameF data)
open GaussianEulerPositivePowerChartMesh (timeNumerator timeDenominator node_source)
open GaussianEulerPowerChartTimeOrder (chart_time_order order_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianGammaCanonicalExponent (constantF)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def contains (L U S V a W E : PTm n) : Fm PTm n :=
  le (a*lowerDenominator S V L) E ⋏ le (E*upperNumerator U V L) (a+W)

def gridOrders (e f d h S U V E a W N : PTm n) : Fm PTm n :=
  let D := timeDenominator N E
  realOrder nameF constantF (data e f d h S (timeNumerator zero N a W) D) (fraction d (h*(S*V))) ⋏
    realOrder constantF nameF (fraction (d*(U*V)) h) (data e f d h S (timeNumerator N N a W) D)

theorem enclosing_grid_orders (e f d h Q S L U V E T a W N : PTm n)
    (hu : Γ ⊢[PRAAx] GaussianEulerPowerChartUniformEndpoints.source e f d h Q S L U V)
    (hm : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T a W N)
    (hc : Γ ⊢[PRAAx] contains L U S V a W E) :
    Γ ⊢[PRAAx] gridOrders e f d h S U V E a W N := by
  let A := lowerDenominator S V L
  let B := upperNumerator U V L
  let D := timeDenominator N E
  let P := timeNumerator zero N a W
  let J := timeNumerator N N a W
  let left := data e f d h S P D
  let right := data e f d h S J D
  let fixedLeft := data e f d h S one A
  let fixedRight := data e f d h S B one
  let lo := fraction d (h*(S*V))
  let hi := fraction (d*(U*V)) h
  have physical := uniform_physical_panel S L U V hu.andE₁.andE₂.andE₂.andE₁.andE₂
    hu.andE₂.andE₁.andE₁ hu.andE₂.andE₁.andE₂ hu.andE₂.andE₂.andE₂
  have htLeft := (node_source zero e f d h Q S E T a W N hm (zero_le N)).andE₂.andE₂.andE₁
  have htRight := (node_source N e f d h Q S E T a W N hm (le_refl N)).andE₂.andE₂.andE₁
  have lhs : Γ ⊢[PRAAx] le (P*A) (D*one) :=
    le_congr (by unfold P timeNumerator; ipra_ring) (by unfold D timeDenominator; ipra_ring)
      (mul_le_mul_right N hc.andE₁)
  have rhs : Γ ⊢[PRAAx] le (B*D) (one*J) :=
    le_congr (by unfold D timeDenominator; ipra_ring) (by unfold J timeNumerator; ipra_ring)
      (mul_le_mul_right N hc.andE₂)
  have lower := chart_time_order e f d h Q S P D one A hm.andE₁ htLeft (.andI (le_refl one) physical.andE₁) lhs
  have upper := chart_time_order e f d h Q S B one J D hm.andE₁ (.andI physical.andE₂.andE₁ (le_refl one)) htRight rhs
  have limits := uniform_endpoint_order e f d h Q S L U V hu
  exact .andI (order_trans nameF nameF constantF left fixedLeft lo lower limits.andE₁)
    (order_trans constantF nameF nameF hi fixedRight right limits.andE₂ upper)

theorem actual_original_enclosing_chart_grid_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      ((GaussianEulerPowerChartUniformEndpoints.source
          (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
        GaussianEulerPositivePowerChartMesh.source
          (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 9) (var 10) (var 11) (var 12) (var 13)) ⋏
        contains (var 6) (var 7) (var 5) (var 8) (var 11) (var 12) (var 9) ⟶
          gridOrders (var 0) (var 1) (var 2) (var 3) (var 5) (var 7) (var 8)
            (var 9) (var 11) (var 12) (var 13)) :=
  closeUniv 14 (.impI (enclosing_grid_orders _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartEnclosingOrders
