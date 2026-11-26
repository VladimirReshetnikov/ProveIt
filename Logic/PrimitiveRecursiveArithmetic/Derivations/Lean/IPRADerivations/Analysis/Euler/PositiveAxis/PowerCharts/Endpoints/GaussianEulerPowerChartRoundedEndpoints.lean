import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartEquivalentTimes
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartRoundedEndpointOrder

/-!
# Cofinality of the literal rounded power-chart panels

The corrected first and last nodes enclose the requested reference
interval. The bound includes the upward tilt and retains the original
retimed power chart observation at each endpoint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartRoundedEndpoints

open_ipra
open GaussianEulerPowerChartCofinalEndpoints (source lowerDenominator upperNumerator width)
open GaussianEulerPositivePowerChart (nameF data)
open GaussianEulerPositivePowerChartMesh (node timeNumerator timeDenominator node_source)
open GaussianEulerPositivePowerChartImage (query)
open GaussianEulerPositivePowerChartCorrectedImage (imageNumerator imageDenominator imageFraction)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameEquivalence (crossEquivalent diagonal_at cross_to_diagonal)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def chartBudget (N V : PTm n) : PTm n := (two*N+two)*V

theorem corrected_node_distance (k i e f d h Q S E T a C N V x y : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T a C N)
    (hi : Γ ⊢[PRAAx] le i N) (hV : Γ ⊢[PRAAx] le one V)
    (hk : Γ ⊢[PRAAx] le (chartBudget N V) (unit (query k h Q E T)))
    (exactValue : Γ ⊢[PRAAx] crossEquivalent nameF constantF
      (data e f d h S (timeNumerator i N a C) (timeDenominator N E)) (fraction x y)) :
    Γ ⊢[PRAAx] distanceBounded (imageFraction k i e f d h Q S E T a C N) (fraction x y) one V := by
  let p := query k h Q E T
  let w := node k i e f d h Q S E T a C N
  let q := fraction (GaussianUnitIntervalInputDecoding.numerator w) (GaussianUnitIntervalInputDecoding.denominator w)
  let out := imageFraction k i e f d h Q S E T a C N
  have sampled : Γ ⊢[PRAAx] distanceBounded w (ap2 constantF p (fraction x y)) two (unit p) :=
    diagonal_at nameF constantF _ _ p (cross_to_diagonal _ _ _ _ exactValue)
  have raw : Γ ⊢[PRAAx] w ≐ q :=
    (GaussianEulerPositivePowerChartImage.fraction_exact k e f d h Q S E T _ _
      (node_source i e f d h Q S E T a C N hs hi)).eqSymm
  have base : Γ ⊢[PRAAx] distanceBounded q (fraction x y) two (unit p) :=
    distance_congr raw (constant_at p (fraction x y)) (.eqRefl _) (.eqRefl _) sampled
  have corrected : Γ ⊢[PRAAx] distanceBounded out q (two*N) (unit p) :=
    GaussianEulerPositivePowerChartCorrectedImage.original_displacement k i e f d h Q S E T a C N hs hi
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) hV
    (le_congr (.eqRefl _) (by ipra_ring) hk)
    (distance_triangle_same out q (fraction x y) (two*N) two (unit p) (unit_positive p) corrected base)

def containsPanel (k e f d h Q S V N H J : PTm n) : Fm PTm n :=
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  let a := GaussianEulerPositivePowerChartCorrectedPanel.start k e f d h Q S E T one C N
  let D := GaussianEulerPositivePowerChartCorrectedPanel.denominator k e f d h Q S E T one C N
  let L := GaussianEulerPositivePowerChartCorrectedPanel.span k e f d h Q S E T one C N
  le (a*H) D ⋏ le (J*D) (a+L)

theorem original_rounded_panel_contains (k e f d h Q S V N H J : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S V) (hN : Γ ⊢[PRAAx] le one N)
    (hH : Γ ⊢[PRAAx] le (two*H) V) (hJ : Γ ⊢[PRAAx] le (J+one) V)
    (hk : Γ ⊢[PRAAx] le (chartBudget N V)
      (unit (query k h Q (lowerDenominator S V f) (upperNumerator h V f)))) :
    Γ ⊢[PRAAx] containsPanel k e f d h Q S V N H J := by
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  let b := h*lowerDenominator S V e
  let c := d*upperNumerator h V e
  let A := imageNumerator k zero e f d h Q S E T one C N
  let B := imageDenominator k zero e f d h Q S E T one C N
  let M := imageNumerator k N e f d h Q S E T one C N
  let D := imageDenominator k N e f d h Q S E T one C N
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) hs.andE₂
  have hh := hs.andE₁.andE₂.andE₁.andE₂
  have phys := GaussianEulerPowerChartCofinalEndpoints.physical_panel e f d h Q S V hs
  have images := GaussianEulerPowerChartCofinalEndpoints.image_guards e f d h Q S V hs
  have mesh : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T one C N :=
    .andI hs.andE₁ (.andI phys.andE₁ (.andI (le_refl _)
      (.andI (le_congr phys.andE₂.andE₂.andE₂.eqSymm (.eqRefl _) (le_refl (T*E))) hN)))
  have native : Γ ⊢[PRAAx] le (two*N) (chartBudget N V) := by
    unfold chartBudget
    ipra_le 𝔞(two*N)*sl hV+𝔞(two*V)
  have positiveInput : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartCorrectedImage.input k e f d h Q S E T one C N :=
    .andI mesh (le_trans native hk)
  have posL := (GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k zero e f d h Q S E T one C N
    positiveInput (zero_le N)).andE₁.andE₂
  have posR := (GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k N e f d h Q S E T one C N
    positiveInput (le_refl N)).andE₁.andE₂
  have endpoints := GaussianEulerPowerChartEquivalentTimes.exact_grid_endpoints e f d h Q S V N hs hN
  have low := corrected_node_distance k zero e f d h Q S E T one C N V d b mesh (zero_le N) hV hk endpoints.andE₁
  have high := corrected_node_distance k N e f d h Q S E T one C N V c h mesh (le_refl N) hV hk endpoints.andE₂
  have lowNative := GaussianEulerPowerChartRoundedEndpointOrder.lower_containment A B d b V H posL images.andE₁ hV
    images.andE₂.andE₁ hH low
  have highNative := GaussianEulerPowerChartRoundedEndpointOrder.upper_containment M D c h V J posR hh hV
    images.andE₂.andE₂ hJ high
  have lower : Γ ⊢[PRAAx] le ((A*D)*H) (B*D) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right D lowNative)
  have upper : Γ ⊢[PRAAx] le (J*(B*D)) (M*B) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right B highNative)
  exact .andI lower (le_congr (.eqRefl _)
    (GaussianEulerPositivePowerChartCorrectedPanel.endpoint_identity k e f d h Q S E T one C N mesh).eqSymm upper)

theorem actual_corrected_power_chart_cofinal_panel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⋏ le one (var 8)) ⋏
      ((le (two*var 9) (var 7) ⋏ le (var 10+one) (var 7)) ⋏
        le (chartBudget (var 8) (var 7)) (unit (query (var 0) (var 4) (var 5)
          (lowerDenominator (var 6) (var 7) (var 2)) (upperNumerator (var 4) (var 7) (var 2)))))) ⟶
      containsPanel (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) :=
  closeUniv 11 (.impI (original_rounded_panel_contains _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁.andE₁
    Prf.hyp0.andE₂.andE₁.andE₂ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartRoundedEndpoints
