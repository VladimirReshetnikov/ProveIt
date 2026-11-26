import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartCofinalEndpoints
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartExponentOrder

/-!
# Uniform physical endpoints for the original rational power chart

With (1/H\le e/f), (1/C\le d/h\le S), and (V\ge2), the same
physical interval ([1/(SV)^H,(CV)^H]) works for every allowed
numerator and denominator. The comparison chart uses the exact
rational exponent (1/H) at both powered endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformEndpoints

open_ipra
open GaussianEulerPositivePowerChart (parameters nameF data)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator physicalPanel)
open GaussianEulerPowerChartExponentOrder (increasing_power decreasing_power scaled_order)
open GaussianEulerPowerChartRationalPowers (original_chart_value chart_proper)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (e f d h Q S H C V : PTm n) : Fm PTm n :=
  parameters e f d h Q S ⋏ ((le one H ⋏ le one C) ⋏
    ((le f (e*H) ⋏ le h (d*C)) ⋏ le two V))

def endpointOrder (e f d h S H C V : PTm n) : Fm PTm n :=
  let E := lowerDenominator S V H
  let T := upperNumerator C V H
  realOrder nameF constantF (data e f d h S one E) (fraction d (h*(S*V))) ⋏
    realOrder constantF nameF (fraction (d*(C*V)) h) (data e f d h S T one)

def referenceBounds (d h S C V : PTm n) : Fm PTm n :=
  le (d*V) (h*(S*V)) ⋏ le (h*V) (d*(C*V))

private theorem one_le_two : Γ ⊢[PRAAx] le one two :=
  le_of_eq_add (d := one) (by ipra_ring)

private alias right_one := Common.mul_one_right

private theorem unit_parameters (H d h Q S : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hd : Γ ⊢[PRAAx] le one d)
    (hh : Γ ⊢[PRAAx] le one h) (hQ : Γ ⊢[PRAAx] le one Q)
    (hS : Γ ⊢[PRAAx] le one S) (hScale : Γ ⊢[PRAAx] le d (S*h)) :
    Γ ⊢[PRAAx] parameters one H d h Q S :=
  .andI (.andI (le_refl one) hH) (.andI (.andI hd hh)
    (.andI (.andI hQ hS) (.andI (positive_product Q H hQ hH) hScale)))

theorem uniform_physical_panel (S H C V : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hH : Γ ⊢[PRAAx] le one H)
    (hC : Γ ⊢[PRAAx] le one C) (hV : Γ ⊢[PRAAx] le two V) :
    Γ ⊢[PRAAx] physicalPanel H C S V :=
  GaussianEulerPowerChartCofinalEndpoints.physical_panel one H one C one S V
    (.andI (unit_parameters H one C one S hH (le_refl one) hC (le_refl one) hS
      (positive_product S C hS hC)) hV)

theorem uniform_reference_bounds (d h S C V : PTm n)
    (hLeft : Γ ⊢[PRAAx] le d (S*h)) (hRight : Γ ⊢[PRAAx] le h (d*C)) :
    Γ ⊢[PRAAx] referenceBounds d h S C V :=
  .andI (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right V hLeft))
    (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right V hRight))

private theorem reference_value (H d h Q S a b : PTm n)
    (hp : Γ ⊢[PRAAx] parameters one H d h Q S)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF
      (data one H d h S (pw a H) (pw b H)) (fraction (d*a) (h*b)) := by
  let u := pw a H
  let v := pw b H
  have hs := GaussianHarmonicLogarithmPower.power_source a b H ht
  have chart : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source one H d h Q S v u u v :=
    .andI hp (.andI hs.andE₂ (GaussianHarmonicLogarithmPower.compact_domain u v hs))
  have raw := original_chart_value one H d h Q S v u a b ht chart
  have eq := GaussianEulerPositivePowerChartJacobian.fraction_congr (Γ := Γ)
    (congrMul (.eqRefl d) (pw_one a)) (congrMul (.eqRefl h) (pw_one b))
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr nameF constantF _ _ _ _
    (.eqRefl _) eq raw

private theorem lower_reference (H d h Q S V : PTm n)
    (hp : Γ ⊢[PRAAx] parameters one H d h Q S)
    (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx] crossEquivalent nameF constantF
      (data one H d h S one (lowerDenominator S V H)) (fraction d (h*(S*V))) := by
  let b := S*V
  let E := lowerDenominator S V H
  have ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one b :=
    .andI (le_refl one) (positive_product S V hp.andE₂.andE₂.andE₁.andE₂ hV)
  have powered := GaussianHarmonicLogarithmPower.power_source one b H ht
  have eq : Γ ⊢[PRAAx] pw one H ≐ one := pw_one_base H
  have proper := chart_proper one H d h Q S one E (pw one H) E hp
    (.andI (le_refl one) powered.andE₂) powered
    ((mul_comm one E).eqTrans (congrMul (.eqRefl E) eq.eqSymm))
  have value := reference_value H d h Q S one b hp ht
  have converted := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF constantF _ _ _ _
    (.eqRefl _) (GaussianEulerPositivePowerChartJacobian.fraction_congr (right_one d) (.eqRefl (h*b))) value
  exact cross_trans _ _ _ _ _ _ proper converted

private theorem upper_reference (H C d h Q S V : PTm n)
    (hp : Γ ⊢[PRAAx] parameters one H d h Q S)
    (hC : Γ ⊢[PRAAx] le one C) (hV : Γ ⊢[PRAAx] le one V) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF
      (data one H d h S (upperNumerator C V H) one) (fraction (d*(C*V)) h) := by
  let a := C*V
  let T := upperNumerator C V H
  have ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a one :=
    .andI (positive_product C V hC hV) (le_refl one)
  have powered := GaussianHarmonicLogarithmPower.power_source a one H ht
  have eq : Γ ⊢[PRAAx] pw one H ≐ one := pw_one_base H
  have proper := chart_proper one H d h Q S T one T (pw one H) hp
    (.andI powered.andE₁ (le_refl one)) powered
    ((congrMul (.eqRefl T) eq).eqTrans (mul_comm T one))
  have value := reference_value H d h Q S a one hp ht
  have converted := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF constantF _ _ _ _
    (.eqRefl _) (GaussianEulerPositivePowerChartJacobian.fraction_congr (.eqRefl (d*a)) (right_one h)) value
  exact cross_trans _ _ _ _ _ _ proper converted

private theorem compare_source (e f d h Q S H C V a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S H C V)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] GaussianEulerPowerChartExponentOrder.source one H e f Q a b :=
  .andI (.andI hs.andE₂.andE₁.andE₁
    (positive_product Q H hs.andE₁.andE₂.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₁))
    (.andI (.andI hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₂.andE₂.andE₁)
      (.andI (le_congr (one_mul f).eqSymm (.eqRefl _) hs.andE₂.andE₂.andE₁.andE₁) ht))

theorem uniform_endpoint_order (e f d h Q S H C V : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S H C V) :
    Γ ⊢[PRAAx] endpointOrder e f d h S H C V := by
  let E := lowerDenominator S V H
  let T := upperNumerator C V H
  let l := data e f d h S one E
  let r := data e f d h S T one
  let l' := data one H d h S one E
  let r' := data one H d h S T one
  let L := fraction d (h*(S*V))
  let U := fraction (d*(C*V)) h
  have hp := hs.andE₁
  have hh := hp.andE₂.andE₁.andE₂
  have hS := hp.andE₂.andE₂.andE₁.andE₂
  have hScale := hp.andE₂.andE₂.andE₂.andE₂
  have hH := hs.andE₂.andE₁.andE₁
  have hC := hs.andE₂.andE₁.andE₂
  have hV : Γ ⊢[PRAAx] le one V := le_trans one_le_two hs.andE₂.andE₂.andE₂
  have physical := uniform_physical_panel S H C V hS hH hC hs.andE₂.andE₂.andE₂
  have hE : Γ ⊢[PRAAx] le one E := physical.andE₁
  have hT : Γ ⊢[PRAAx] le one T := physical.andE₂.andE₁
  have lh : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one E := .andI (le_refl _) hE
  have rh : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source T one := .andI hT (le_refl _)
  have reference := unit_parameters H d h Q S hH hp.andE₂.andE₁.andE₁ hh hp.andE₂.andE₂.andE₁.andE₁ hS hScale
  have left := scaled_order e f one H d h S one E hh hScale
    (decreasing_power one H e f Q one E (compare_source e f d h Q S H C V one E hs lh) hE)
  have right := scaled_order one H e f d h S T one hh hScale
    (increasing_power one H e f Q T one (compare_source e f d h Q S H C V T one hs rh) hT)
  have selfL : Γ ⊢[PRAAx] crossEquivalent nameF nameF l l := chart_proper e f d h Q S one E one E hp lh lh (mul_comm one E)
  have selfR : Γ ⊢[PRAAx] crossEquivalent nameF nameF r r := chart_proper e f d h Q S T one T one hp rh rh (mul_comm T one)
  have eqL := lower_reference H d h Q S V reference hV
  have eqR := upper_reference H C d h Q S V reference hC hV
  exact .andI
    (GaussianNamedRealOrderTransport.transport nameF nameF nameF constantF l l l' L selfL eqL left)
    (GaussianNamedRealOrderTransport.transport constantF nameF nameF nameF U r' r r
      (cross_symm nameF constantF r' U eqR) selfR right)

theorem actual_original_power_chart_uniform_endpoints_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        (physicalPanel (var 6) (var 7) (var 5) (var 8) ⋏
          (endpointOrder (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) ⋏
            referenceBounds (var 2) (var 3) (var 5) (var 7) (var 8)))) := by
  apply closeUniv 9
  refine .impI (.andI ?_ (.andI ?_ ?_))
  · exact uniform_physical_panel _ _ _ _ Prf.hyp0.andE₁.andE₂.andE₂.andE₁.andE₂
      Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂ Prf.hyp0.andE₂.andE₂.andE₂
  · exact uniform_endpoint_order _ _ _ _ _ _ _ _ _ Prf.hyp0
  · exact uniform_reference_bounds _ _ _ _ _ Prf.hyp0.andE₁.andE₂.andE₂.andE₂.andE₂ Prf.hyp0.andE₂.andE₂.andE₁.andE₂

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformEndpoints
