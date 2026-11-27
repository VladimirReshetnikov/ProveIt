import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.Cofinal.GaussianEulerPowerChartCofinalSchedule
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.Quadrature.GaussianEulerPositivePowerChartImageSchedule
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactExhaustionComposition
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactExhaustionImageLattice
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactExhaustionNormalization

/-!
# Cofinal observations of the original rational power-damped integral

The output is one ordinary compact source observation at explicit physical
cutoffs. The comparison tracks the original corrected image sum, an
independently counted ordinary image quadrature, and the actual Gamma name
at the rescaled argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCofinalObservation

open_ipra
open GaussianEulerPowerChartCofinalSchedule (source cutoffSize samplingIndex)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianEulerPowerScalingGridSchedule (count precision imagePrecision)
open GaussianEulerPowerScalingCell (scaleBound scaleSample)
open GaussianEulerPowerScalingCorrectedQuadrature (correctedSum)
open GaussianEulerCompactExhaustionScaled (referenceF referenceData cutoff clock)
open GaussianEulerPositivePowerChartImageSchedule (target)
open GaussianFastValueCut (exponent query_budget)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure Grid (n : ℕ) where
  cutoffIndex : PTm n
  lower : PTm n
  upper : PTm n
  span : PTm n
  imageClock : PTm n
  requestedStage : PTm n
  stage : PTm n
  cells : PTm n
  sourceClock : PTm n
  chartClock : PTm n

def grid (s z R B A e f d h L Q S : PTm n) : Grid n :=
  let τ := s+two
  let j := cutoff τ z R B A e f d h L Q
  let V := cutoffSize j (Q*A) (L*R)
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  let r := exponent (two*scaleBound z B e f d h) τ
  let v := target r (L*R) h Q S E T C+clock τ z R B A e f d h L Q+exponent (Q+one) τ
  let t := samplingIndex v V
  let N := count t z R B e f d h L Q S E T C
  ⟨j,E,T,C,r,v,t,N,precision t z R B e f d h L Q S E T C,imagePrecision t z R B e f d h L Q S E T C N⟩

def observation (s z R B A e f d h L Q S : PTm n) : PTm n :=
  let G := grid s z R B A e f d h L Q S
  ap2 GaussianEulerPowerScalingCompactName.nameF G.stage
    (GaussianEulerPowerScalingCompactName.data z R B e f d h Q S one G.span G.lower G.upper)

private theorem compatible_source (s z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) :
    let G := grid s z R B A e f d h L Q S
    Γ ⊢[PRAAx] GaussianEulerPowerScalingGridSchedule.source z R B A e f d h L Q S G.lower G.upper one G.span := by
  dsimp only
  let τ := s+two
  let j := cutoff τ z R B A e f d h L Q
  let V := cutoffSize j (Q*A) (L*R)
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let C := width f h S V
  have v := (GaussianEulerPowerChartCofinalSchedule.cutoff_guards (Γ := Γ) j (Q*A) (L*R)).andE₁
  have panel := GaussianEulerPowerChartCofinalEndpoints.physical_panel e f d h Q S V (.andI hs.andE₂ v)
  show Γ ⊢[PRAAx] GaussianEulerPowerScalingGridSchedule.source z R B A e f d h L Q S E T one C
  exact .andI hs.andE₁ (.andI hs.andE₂ (.andI panel.andE₁ (.andI (le_refl _)
    (le_congr panel.andE₂.andE₂.andE₂.eqSymm (.eqRefl _) (le_refl (T*E))))))

theorem source_clock_later (t z R B e f d h L Q S E T C : PTm n) :
    Γ ⊢[PRAAx] le t (precision t z R B e f d h L Q S E T C) := by
  unfold precision GaussianCompactRiemannName.precision
  exact le_trans (le_trans (le_add_right t T) (le_add_right _ _)) (le_add_right _ _)

def correctedObservation (G : Grid n) (z B e f d h Q S : PTm n) : PTm n :=
  correctedSum G.sourceClock G.chartClock z B e f d h Q S G.lower G.upper one G.span G.cells

def ordinaryImageObservation (G : Grid n) (z R B e f d h L Q S : PTm n) : PTm n :=
  GaussianEulerPositivePowerChartImageName.observation G.imageClock G.chartClock z (L*R)
    B e f d h Q S G.lower G.upper one G.span G.cells

theorem staged_comparisons (s z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) :
    let G := grid s z R B A e f d h L Q S
    let scale := scaleSample G.sourceClock z B e f d h
    Γ ⊢[PRAAx]
      (distanceBounded (qmul (fraction e f) (observation s z R B A e f d h L Q S))
        (qmul scale (correctedObservation G z B e f d h Q S)) one (unit (s+two)) ⋏
      distanceBounded (qmul scale (correctedObservation G z B e f d h Q S))
        (qmul scale (ordinaryImageObservation G z R B e f d h L Q S)) one (unit (s+two))) := by
  dsimp only
  let G := grid s z R B A e f d h L Q S
  let τ := s+two
  let V := cutoffSize G.cutoffIndex (Q*A) (L*R)
  let I := target G.imageClock (L*R) h Q S G.lower G.upper G.span
  let J := clock τ z R B A e f d h L Q
  let K := exponent (Q+one) τ
  let M := scaleBound z B e f d h
  have hI : Γ ⊢[PRAAx] le I G.stage :=
    le_trans (le_trans (le_add_right I J) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have hK : Γ ⊢[PRAAx] le K G.stage :=
    le_trans (le_add_left K (I+J)) (le_add_right (I+J+K) (two*V))
  have panel := compatible_source s z R B A e f d h L Q S hs
  have first := GaussianEulerPowerScalingGridSchedule.original_scheduled_name_distance G.stage
    z R B A e f d h L Q S G.lower G.upper one G.span panel
  have radiusFirst : Γ ⊢[PRAAx] le ((Q+one)*unit τ) (unit G.stage) :=
    le_trans (query_budget (Q+one) τ) (unit_monotone hK)
  have raw := GaussianEulerPositivePowerChartImageSchedule.original_later_scheduled_ordinary_image
    G.imageClock G.stage z R B A e f d h L Q S G.lower G.upper one G.span panel hI
  let u := correctedObservation G z B e f d h Q S
  let v := ordinaryImageObservation G z R B e f d h L Q S
  have reversed : Γ ⊢[PRAAx] distanceBounded u v two (unit G.imageClock) :=
    distance_symmetric v u two (unit G.imageClock) (unit_positive _) raw
  have guarded : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h :=
    hs.andE₂.andE₂.andE₁
  have scaled := GaussianEulerCompactExhaustionScaleTransport.original_scale_transport G.sourceClock
    z B e f d h u v two (unit G.imageClock) guarded (unit_positive _) reversed
  have radiusSecond : Γ ⊢[PRAAx] le ((M*two)*unit τ) (unit G.imageClock) :=
    le_congr (congrMul (mul_comm two M) (.eqRefl _)) (.eqRefl _) (query_budget (two*M) τ)
  exact .andI
    (distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _) (le_congr (.eqRefl _) (by ipra_ring) radiusFirst) first)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _) (le_congr (.eqRefl _) (by ipra_ring) radiusSecond) scaled)

theorem observation_canonical (s z R B A e f d h L Q S : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (observation s z R B A e f d h L Q S) := by
  let G := grid s z R B A e f d h L Q S
  exact GaussianCompactRiemannName.name_canonical GaussianEulerPowerScalingCompactName.evaluatorF
    G.stage one G.span G.lower (GaussianEulerPowerScalingCompactRate.lipschitz R Q S G.lower G.upper)
    G.upper (GaussianEulerPowerScalingCompactName.fixedData z B e f d h S)

theorem weighted_observations (s q z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction e f) (observation s z R B A e f d h L Q S))
      (ap2 referenceF q (referenceData z R B A e f d h L Q)) (unit s+unit q) (unit s*unit q) := by
  let G := grid s z R B A e f d h L Q S
  let τ := s+two
  let V := cutoffSize G.cutoffIndex (Q*A) (L*R)
  let I := target G.imageClock (L*R) h Q S G.lower G.upper G.span
  let J := clock τ z R B A e f d h L Q
  let K := exponent (Q+one) τ
  let r := G.imageClock
  let p := G.sourceClock
  let k := G.chartClock
  have hI : Γ ⊢[PRAAx] le I G.stage :=
    le_trans (le_trans (le_add_right I J) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have hJ : Γ ⊢[PRAAx] le J G.stage :=
    le_trans (le_trans (le_add_left J I) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have later : Γ ⊢[PRAAx] le G.stage p :=
    source_clock_later G.stage z R B e f d h L Q S G.lower G.upper G.span
  have hr : Γ ⊢[PRAAx] le r p := le_trans
    (GaussianEulerPositivePowerChartImageSchedule.target_later r (L*R) h Q S G.lower G.upper G.span)
    (le_trans hI later)
  have panel := compatible_source s z R B A e f d h L Q S hs
  have corrected := GaussianEulerPositivePowerChartImageSchedule.scheduled_corrected_source
    G.stage z R B A e f d h L Q S G.lower G.upper one G.span panel
  have cofinal := GaussianEulerPowerChartCofinalSchedule.original_scheduled_image_source
    G.cutoffIndex G.requestedStage z R B A e f d h L Q S hs
  have imageSource := GaussianEulerCompactExhaustionImageLattice.original_scaled_lattice_source
    r G.cutoffIndex k z R B A e f d h L Q S G.lower G.upper one G.span G.cells
    hs.andE₁ corrected.andE₂ cofinal
  let x := GaussianEulerPositivePowerChartImageCuts.data k e f d h Q S G.lower G.upper one G.span G.cells
  let F := GaussianEulerPositivePowerChartImageName.latticeFactor r (L*R) h Q S G.lower G.upper
  let a := GaussianEulerPositivePowerChartImageCuts.start G.cells x F
  let C := GaussianEulerPositivePowerChartImageCuts.count G.cells x F
  let D := GaussianEulerPositivePowerChartImageCuts.denominator G.cells x F
  let H := GaussianEulerPositivePowerChartImage.reciprocalMargin h Q G.lower G.upper
  let T := GaussianEulerPositivePowerChartImageName.panelTop Q S G.lower G.upper
  have third := GaussianEulerCompactExhaustionComposition.paid_independent_image_clock τ p r q
    z R B A e f d h L Q G.cutoffIndex a C D H T imageSource (le_refl _)
    (le_trans hJ later) hr (query_budget (two*scaleBound z B e f d h) τ)
  have first := staged_comparisons s z R B A e f d h L Q S hs
  exact GaussianEulerCompactExhaustionComposition.three_paid_comparisons s q _ _ _ _
    first.andE₁ first.andE₂ third

theorem original_observations (p q z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) :
    Γ ⊢[PRAAx] distanceBounded
      (observation (GaussianEulerCompactExhaustionNormalization.referenceClock p L) z R B A e f d h L Q S)
      (ap2 GaussianEulerCompactExhaustionNormalization.nameF q
        (GaussianEulerCompactExhaustionNormalization.data z R B A e f d h L Q))
      (unit p+unit q) (unit p*unit q) := by
  let s := GaussianEulerCompactExhaustionNormalization.referenceClock p L
  let u := GaussianEulerCompactExhaustionNormalization.referenceClock q L
  exact GaussianEulerCompactExhaustionNormalization.remove_chart_coefficient_at_paid_clock
    p s q _ z R B A e f d h L Q hs.andE₁ (observation_canonical s z R B A e f d h L Q S)
    (GaussianEulerCompactExhaustionNormalization.paid_clock p L)
    (weighted_observations s u z R B A e f d h L Q S hs)

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCofinalObservation
