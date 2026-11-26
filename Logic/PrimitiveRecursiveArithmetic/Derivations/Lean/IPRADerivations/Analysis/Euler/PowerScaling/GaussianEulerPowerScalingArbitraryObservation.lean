import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingUniformObservation
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartEnclosingSchedule

/-!
# Original Euler quadrature observations on an arbitrary enclosing panel

The panel's endpoint data are independent of the sampling schedule. Its
original affine quadrature uses the same corrected image comparison and
normalization as the prescribed physical panel, once containment of the
actual image grid has been established.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingArbitraryObservation

open_ipra
open GaussianEulerPowerChartUniformSchedule (panelStage)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize samplingIndex)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianEulerPowerScalingGridSchedule (source count precision imagePrecision)
open GaussianEulerPowerScalingCofinalObservation (Grid source_clock_later)
open GaussianEulerPowerScalingCorrectedQuadrature (correctedSum)
open GaussianEulerPowerScalingCell (scaleBound scaleSample)
open GaussianEulerCompactExhaustionScaled (cutoff referenceF referenceData clock)
open GaussianEulerCompactExhaustionNormalization (referenceClock)
open GaussianEulerPositivePowerChartImageSchedule (target)
open GaussianEulerPowerScalingImproper (formulaF formulaData resultF resultData)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianFastValueCut (exponent query_budget)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "compactF" => GaussianEulerPowerScalingCompactName.nameF
local notation "compactData" => GaussianEulerPowerScalingCompactName.data

def grid (s j z R B A e f d h L Q S E T W : PTm n) : Grid n :=
  let τ := panelStage s L+two
  let V := cutoffSize j (Q*A) (L*R)
  let r := exponent (two*scaleBound z B e f d h) τ
  let v := target r (L*R) h Q S E T W+clock τ z R B A e f d h L Q+exponent (Q+one) τ
  let t := samplingIndex v V
  let N := count t z R B e f d h L Q S E T W
  ⟨j,E,T,W,r,v,t,N,precision t z R B e f d h L Q S E T W,imagePrecision t z R B e f d h L Q S E T W N⟩

def imageSource (s j z R B A e f d h L Q S E T a W : PTm n) : Fm PTm n :=
  let G := grid s j z R B A e f d h L Q S E T W
  let p := G.chartClock
  let N := G.cells
  GaussianEulerCompactExhaustion.source (GaussianEulerPowerScalingParameter.scaled z f) (L*R) (B*e) (Q*A) j
    (GaussianEulerPositivePowerChartCorrectedPanel.start p e f d h Q S E T a W N)
    (GaussianEulerPositivePowerChartCorrectedPanel.span p e f d h Q S E T a W N)
    (GaussianEulerPositivePowerChartCorrectedPanel.denominator p e f d h Q S E T a W N)
    (GaussianEulerPositivePowerChartImage.reciprocalMargin h Q E T) (GaussianEulerPositivePowerChartImageName.panelTop Q S E T)

theorem compact_source (z R B A e f d h L Q S E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W) :
    Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactName.source z R B e f d h Q S a W E T := by
  have cert := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  exact .andI (.andI (.andI cert.andE₁ (.andI hs.andE₂.andE₂.andE₁ cert.andE₂))
    (.andI hs.andE₂.andE₂.andE₂.andE₁ (le_congr (.eqRefl _) (mul_comm T E) hs.andE₂.andE₂.andE₂.andE₂))) hs.andE₂.andE₁

private theorem weighted (s q j z R B A e f d h L Q S E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W)
    (hj : Γ ⊢[PRAAx] le (cutoff (panelStage s L+two) z R B A e f d h L Q) j)
    (hi : Γ ⊢[PRAAx] imageSource s j z R B A e f d h L Q S E T a W) :
    let G := grid s j z R B A e f d h L Q S E T W
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction e f) (ap2 compactF G.stage (compactData z R B e f d h Q S a W E T)))
      (ap2 referenceF q (referenceData z R B A e f d h L Q))
      (unit (panelStage s L)+unit q) (unit (panelStage s L)*unit q) := by
  dsimp only
  let G := grid s j z R B A e f d h L Q S E T W
  let τ := panelStage s L+two
  let V := cutoffSize j (Q*A) (L*R)
  let I := target G.imageClock (L*R) h Q S E T W
  let J := clock τ z R B A e f d h L Q
  let K := exponent (Q+one) τ
  let m := scaleBound z B e f d h
  let r := G.imageClock
  let p := G.sourceClock
  let k := G.chartClock
  let u := correctedSum p k z B e f d h Q S E T a W G.cells
  let v := GaussianEulerPositivePowerChartImageName.observation r k z (L*R) B e f d h Q S E T a W G.cells
  have hI : Γ ⊢[PRAAx] le I G.stage :=
    le_trans (le_trans (le_add_right I J) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have hJ : Γ ⊢[PRAAx] le J G.stage :=
    le_trans (le_trans (le_add_left J I) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have hK : Γ ⊢[PRAAx] le K G.stage := le_trans (le_add_left K (I+J)) (le_add_right (I+J+K) (two*V))
  have later : Γ ⊢[PRAAx] le G.stage p := source_clock_later G.stage z R B e f d h L Q S E T W
  have hr : Γ ⊢[PRAAx] le r p := le_trans
    (GaussianEulerPositivePowerChartImageSchedule.target_later r (L*R) h Q S E T W) (le_trans hI later)
  have first := GaussianEulerPowerScalingGridSchedule.original_scheduled_name_distance G.stage z R B A e f d h L Q S E T a W hs
  have rFirst : Γ ⊢[PRAAx] le ((Q+one)*unit τ) (unit G.stage) := le_trans (query_budget (Q+one) τ) (unit_monotone hK)
  have raw := GaussianEulerPositivePowerChartImageSchedule.original_later_scheduled_ordinary_image r G.stage z R B A e f d h L Q S E T a W hs hI
  have reversed : Γ ⊢[PRAAx] distanceBounded u v two (unit r) := distance_symmetric _ _ _ _ (unit_positive _) raw
  have scaled := GaussianEulerCompactExhaustionScaleTransport.original_scale_transport p z B e f d h u v two (unit r)
    hs.andE₂.andE₁.andE₂.andE₁ (unit_positive _) reversed
  have rSecond : Γ ⊢[PRAAx] le ((two*m)*unit τ) (unit r) := query_budget (two*m) τ
  have rScaled : Γ ⊢[PRAAx] le ((m*two)*unit τ) (unit r) :=
    le_congr (congrMul (mul_comm two m) (.eqRefl _)) (.eqRefl _) rSecond
  have corrected := GaussianEulerPositivePowerChartImageSchedule.scheduled_corrected_source G.stage z R B A e f d h L Q S E T a W hs
  have imageInput := GaussianEulerCompactExhaustionImageLattice.original_scaled_lattice_source r j k z R B A e f d h L Q S E T a W G.cells
    hs.andE₁ corrected.andE₂ hi
  let x := GaussianEulerPositivePowerChartImageCuts.data k e f d h Q S E T a W G.cells
  let F := GaussianEulerPositivePowerChartImageName.latticeFactor r (L*R) h Q S E T
  let u₀ := GaussianEulerPositivePowerChartImageCuts.start G.cells x F
  let w₀ := GaussianEulerPositivePowerChartImageCuts.count G.cells x F
  let E₀ := GaussianEulerPositivePowerChartImageCuts.denominator G.cells x F
  let M := GaussianEulerPositivePowerChartImage.reciprocalMargin h Q E T
  let T₀ := GaussianEulerPositivePowerChartImageName.panelTop Q S E T
  have third := GaussianEulerCompactExhaustionComposition.paid_independent_image_clock τ p r q z R B A e f d h L Q j
    u₀ w₀ E₀ M T₀ imageInput hj (le_trans hJ later) hr rSecond
  exact GaussianEulerCompactExhaustionComposition.three_paid_comparisons (panelStage s L) q _ _ _ _
    (distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _) (le_congr (.eqRefl _) (by ipra_ring) rFirst) first)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
      (le_congr (.eqRefl _) (by ipra_ring) rScaled) scaled) third

private theorem compose (s p q a b c d : PTm n)
    (h₁ : Γ ⊢[PRAAx] distanceBounded a b (unit p+unit (s+num 3)) (unit p*unit (s+num 3)))
    (h₂ : Γ ⊢[PRAAx] distanceBounded b c (unit (s+num 3)+unit (s+num 3)) (unit (s+num 3)*unit (s+num 3)))
    (h₃ : Γ ⊢[PRAAx] distanceBounded c d (unit (s+num 3)+unit q) (unit (s+num 3)*unit q)) :
    Γ ⊢[PRAAx] distanceBounded a d (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let P := unit p
  let Q := unit q
  let W := unit (s+num 3)
  let X := unit s
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hw : Γ ⊢[PRAAx] le one W := unit_positive _
  have pw := positive_product P W hp hw
  have ww := positive_product W W hw hw
  have wq := positive_product W Q hw hq
  have step := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ pw ww h₁ h₂
  have both := positive_product (P*W) (W*W) pw ww
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ both wq step h₃
  have fixed : Γ ⊢[PRAAx] le (num 4) (unit (num 3)) :=
    le_congr (by ipra_ring) (.eqRefl _) (RationalClosure.succ_le_two_pow (num 3))
  have budget : Γ ⊢[PRAAx] le (num 4*X) W :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two s (num 3)).eqSymm) (mul_le_mul_right X fixed)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ both wq)
    (GaussianNamedInverseRate.denominator_positive (unit s) p q (unit_positive s)) _ joined
  unfold rateNumerator rateDenominator
  change Γ ⊢[PRAAx] le _ ((one*P*Q+X*(P+Q))*((P*W*(W*W))*(W*Q)))
  ipra_le 𝔞(P*P*Q*Q*W*W*W)*sl budget

theorem observations_from_image_source (s j p q z R B A e f d h L Q S E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W)
    (hj : Γ ⊢[PRAAx] le (cutoff (panelStage s L+two) z R B A e f d h L Q) j)
    (hi : Γ ⊢[PRAAx] imageSource s j z R B A e f d h L Q S E T a W) : Γ ⊢[PRAAx]
    distanceBounded (ap2 compactF p (compactData z R B e f d h Q S a W E T))
      (ap2 formulaF q (formulaData z R B A e f d h L Q))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let G := grid s j z R B A e f d h L Q S E T W
  let x := compactData z R B e f d h Q S a W E T
  let y := resultData z R B A e f d h L Q
  let w := formulaData z R B A e f d h L Q
  let u := s+num 3
  have input := compact_source z R B A e f d h L Q S E T a W hs
  have regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN compactF x :=
    GaussianEulerPowerScalingCompactName.name_regular z R B e f d h Q S a W E T input
  have canon : Γ ⊢[PRAAx] canonical (ap2 compactF G.stage x) :=
    GaussianCompactRiemannName.name_canonical GaussianEulerPowerScalingCompactName.evaluatorF G.stage
      a W E (GaussianEulerPowerScalingCompactRate.lipschitz R Q S E T) T (GaussianEulerPowerScalingCompactName.fixedData z B e f d h S)
  have hτ : Γ ⊢[PRAAx] le (panelStage s L+two) G.imageClock := le_add_right _ _
  have hStage : Γ ⊢[PRAAx] le (panelStage s L) G.stage := by
    let m := clock (panelStage s L+two) z R B A e f d h L Q
    let v := target G.imageClock (L*R) h Q S E T W
    let K := exponent (Q+one) (panelStage s L+two)
    have hr := GaussianEulerPositivePowerChartImageSchedule.target_later (Γ := Γ) G.imageClock (L*R) h Q S E T W
    exact le_trans (le_add_right _ _) (le_trans hτ (le_trans hr
      (le_trans (le_add_right v m) (le_trans (le_add_right (v+m) K) (le_add_right _ _)))))
  have hp := point_at compactF x p G.stage regular
  have hLater : Γ ⊢[PRAAx] le u G.stage := le_trans (le_add_right u _) hStage
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 compactF p x) (ap2 compactF G.stage x)
      (unit p+unit u) (unit p*unit u) := by
    have hU := unit_monotone hLater
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive _))
      (positive_product _ _ (unit_positive p) (unit_positive _)) _ hp
    ipra_le 𝔞(unit p*unit p)*sl hU
  have middle := GaussianEulerCompactExhaustionNormalization.remove_chart_coefficient_at_paid_clock
    u (panelStage s L) u (ap2 compactF G.stage x) z R B A e f d h L Q hs.andE₁ canon
    (GaussianEulerCompactExhaustionNormalization.paid_clock u L)
    (weighted s (referenceClock u L) j z R B A e f d h L Q S E T a W hs hj hi)
  have base := GaussianEulerCompactExhaustionScaled.reference_regular z R B A e f d h L Q hs.andE₁ hs.andE₂.andE₁.andE₂.andE₁
  have inv := GaussianEulerCompactExhaustionNormalization.inverse_bound e f L
    hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have eq : Γ ⊢[PRAAx] crossEquivalent resultF formulaF y w :=
    GaussianBoundedConstantProductName.ordinary_product_identity referenceF L (fraction f e) _ (.andI base inv)
  exact compose s p q _ _ _ _ first middle (cross_at resultF formulaF y w u q eq)

theorem original_enclosing_observations (s j p q z R B A e f d h L Q S U E T a W : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a W)
    (hU : Γ ⊢[PRAAx] le one U) (hu : Γ ⊢[PRAAx] le h (d*U))
    (hj : Γ ⊢[PRAAx] le (cutoff (panelStage s L+two) z R B A e f d h L Q) j)
    (hleft : Γ ⊢[PRAAx] le (a*lowerDenominator S (cutoffSize j (Q*A) (L*R)) L) E)
    (hright : Γ ⊢[PRAAx] le (E*upperNumerator U (cutoffSize j (Q*A) (L*R)) L) (a+W)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 compactF p (compactData z R B e f d h Q S a W E T))
      (ap2 formulaF q (formulaData z R B A e f d h L Q))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) :=
  observations_from_image_source s j p q z R B A e f d h L Q S E T a W hs hj
    (GaussianEulerPowerChartEnclosingSchedule.original_enclosing_image_source j
      (grid s j z R B A e f d h L Q S E T W).requestedStage z R B A e f d h L Q S U E T a W hs hU hu hleft hright)

theorem actual_original_enclosing_power_damped_panel_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 20
    (source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
      (var 12) (var 13) (var 14) (var 16) (var 17) (var 18) (var 19) ⟶
      le one (var 15) ⟶ le (var 11) (var 10*var 15) ⟶
      le (cutoff (panelStage (var 0) (var 12)+two) (var 4) (var 5) (var 6) (var 7)
        (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)) (var 1) ⟶
      le (var 18*lowerDenominator (var 14) (cutoffSize (var 1) (var 13*var 7) (var 12*var 5)) (var 12)) (var 16) ⟶
      le (var 16*upperNumerator (var 15) (cutoffSize (var 1) (var 13*var 7) (var 12*var 5)) (var 12)) (var 18+var 19) ⟶
      distanceBounded (ap2 compactF (var 2) (compactData (var 4) (var 5) (var 6) (var 8) (var 9)
        (var 10) (var 11) (var 13) (var 14) (var 18) (var 19) (var 16) (var 17)))
        (ap2 formulaF (var 3) (formulaData (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)))
        (rateNumerator one (unit (var 0)) (var 2) (var 3)) (rateDenominator (unit (var 0)) (var 2) (var 3))) :=
  closeUniv 20 (.impI (.impI (.impI (.impI (.impI (.impI (original_enclosing_observations
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingArbitraryObservation
