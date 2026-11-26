import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerChartUniformSchedule
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerScalingImproper

/-!
# The original rational Euler quadrature on a uniform physical panel

The panel is fixed before the rational parameters are decoded. Its
ordinary compact observations compare to the original Gamma-side
formula at independent clocks. The construction pays for the exact
rational chart refinement after the panel has been chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingUniformObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerChartUniformSchedule (panelStage cutoffIndex cutoff_later original_uniform_image_source)
open GaussianEulerPowerChartUniformEndpoints (uniform_physical_panel)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize samplingIndex cutoff_guards)
open GaussianEulerPowerScalingGridSchedule (count precision imagePrecision)
open GaussianEulerPowerScalingCofinalObservation (Grid correctedObservation ordinaryImageObservation source_clock_later)
open GaussianEulerPowerScalingCell (scaleBound scaleSample)
open GaussianEulerCompactExhaustionScaled (referenceF referenceData clock)
open GaussianEulerCompactExhaustionNormalization (referenceClock)
open GaussianEulerPositivePowerChartImageSchedule (target)
open GaussianEulerPowerScalingImproper (formulaF formulaData resultF resultData)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianFastValueCut (exponent query_budget)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "compactF" => GaussianEulerPowerScalingCompactName.nameF

def source (z R B A e f d h L Q S U M : PTm n) : Fm PTm n :=
  GaussianEulerPowerChartCofinalSchedule.source z R B A e f d h L Q S ⋏
    ((le one U ⋏ le h (d*U)) ⋏ le (scaleBound z B e f d h) M)

def compactData (s z R B A e f d h L Q S U M : PTm n) : PTm n :=
  let V := cutoffSize (cutoffIndex s (Q*A) (L*R) L M) (Q*A) (L*R)
  GaussianEulerPowerScalingCompactName.data z R B e f d h Q S one
    (width L U S V) (lowerDenominator S V L) (upperNumerator U V L)

@[simp] theorem subst_compactData {m : ℕ} (σ : Fin n → PTm m) (s z R B A e f d h L Q S U M : PTm n) :
    Syn.subst σ (compactData s z R B A e f d h L Q S U M) =
      compactData (Syn.subst σ s) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A)
        (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ L)
        (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ U) (Syn.subst σ M) := by
  simp [compactData,GaussianEulerPowerScalingCompactName.data,cutoffSize,width,lowerDenominator,upperNumerator,
    GaussianGammaIntegralCutoffs.etaDen,GaussianGammaIntegralCutoffs.top,GaussianGammaIntegralCutoffs.height,
    GaussianGammaIntegralCutoffs.tailCoefficient]

private theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A e f d h L Q S U M : PTm n) :
    (source z R B A e f d h L Q S U M).subst σ =
      source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ e)
        (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ L) (Syn.subst σ Q)
        (Syn.subst σ S) (Syn.subst σ U) (Syn.subst σ M) := by
  simp [source,GaussianEulerPowerScalingImproper.subst_source,scaleBound,GaussianEulerPowerScalingKernel.scaleExpData,
    GaussianEulerPowerScalingKernel.scaleData,GaussianGammaFiniteApproximantName.exponentialInputData,
    GaussianEulerPowerScalingParameter.scaled]

private theorem subst_formulaData {m : ℕ} (σ : Fin n → PTm m) (z R B A e f d h L Q : PTm n) :
    Syn.subst σ (formulaData z R B A e f d h L Q) =
      formulaData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ e)
        (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ L) (Syn.subst σ Q) := by
  simp [formulaData,referenceData,GaussianEulerPowerScalingKernel.scaleExpData,
    GaussianEulerPowerScalingKernel.scaleData,GaussianGammaFiniteApproximantName.exponentialInputData,
    GaussianGammaReciprocalInverse.gammaData,GaussianGammaReciprocalInverse.gammaHeight,
    GaussianEulerPowerScalingParameter.scaled]

private def grid (s z R B A e f d h L Q S U M : PTm n) : Grid n :=
  let τ := panelStage s L+two
  let j := cutoffIndex s (Q*A) (L*R) L M
  let V := cutoffSize j (Q*A) (L*R)
  let E := lowerDenominator S V L
  let T := upperNumerator U V L
  let W := width L U S V
  let r := exponent (two*scaleBound z B e f d h) τ
  let v := target r (L*R) h Q S E T W+clock τ z R B A e f d h L Q+exponent (Q+one) τ
  let t := samplingIndex v V
  let N := count t z R B e f d h L Q S E T W
  ⟨j,E,T,W,r,v,t,N,precision t z R B e f d h L Q S E T W,imagePrecision t z R B e f d h L Q S E T W N⟩

private theorem compatible_source (s z R B A e f d h L Q S U M : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S U M) :
    let G := grid s z R B A e f d h L Q S U M
    Γ ⊢[PRAAx] GaussianEulerPowerScalingGridSchedule.source z R B A e f d h L Q S G.lower G.upper one G.span := by
  dsimp only
  let G := grid s z R B A e f d h L Q S U M
  let V := cutoffSize G.cutoffIndex (Q*A) (L*R)
  have hV := (cutoff_guards (Γ := Γ) G.cutoffIndex (Q*A) (L*R)).andE₁
  have panel := uniform_physical_panel S L U V hs.andE₁.andE₂.andE₂.andE₂.andE₁.andE₂
    hs.andE₁.andE₁.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₁.andE₁ hV
  exact .andI hs.andE₁.andE₁ (.andI hs.andE₁.andE₂ (.andI panel.andE₁ (.andI (le_refl _)
    (le_congr panel.andE₂.andE₂.andE₂.eqSymm (.eqRefl _) (le_refl _)))))

private theorem compact_source (s z R B A e f d h L Q S U M : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S U M) :
    let G := grid s z R B A e f d h L Q S U M
    Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactName.source z R B e f d h Q S one G.span G.lower G.upper := by
  dsimp only
  let G := grid s z R B A e f d h L Q S U M
  have geom := compatible_source s z R B A e f d h L Q S U M hs
  have cert := geom.andE₁.andE₁.andE₁.andE₂.andE₁
  have upper := le_congr (.eqRefl _) (mul_comm G.upper G.lower) geom.andE₂.andE₂.andE₂.andE₂
  exact .andI (.andI (.andI cert.andE₁ (.andI geom.andE₂.andE₂.andE₁ cert.andE₂))
    (.andI geom.andE₂.andE₂.andE₂.andE₁ upper)) geom.andE₂.andE₁

private theorem weighted_observations (s q z R B A e f d h L Q S U M : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S U M) :
    let G := grid s z R B A e f d h L Q S U M
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction e f) (ap2 compactF G.stage (compactData s z R B A e f d h L Q S U M)))
      (ap2 referenceF q (referenceData z R B A e f d h L Q))
      (unit (panelStage s L)+unit q) (unit (panelStage s L)*unit q) := by
  dsimp only
  let G := grid s z R B A e f d h L Q S U M
  let τ := panelStage s L+two
  let V := cutoffSize G.cutoffIndex (Q*A) (L*R)
  let I := target G.imageClock (L*R) h Q S G.lower G.upper G.span
  let J := clock τ z R B A e f d h L Q
  let K := exponent (Q+one) τ
  let m := scaleBound z B e f d h
  let r := G.imageClock
  let p := G.sourceClock
  let k := G.chartClock
  let u := correctedObservation G z B e f d h Q S
  let v := ordinaryImageObservation G z R B e f d h L Q S
  have hI : Γ ⊢[PRAAx] le I G.stage :=
    le_trans (le_trans (le_add_right I J) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have hJ : Γ ⊢[PRAAx] le J G.stage :=
    le_trans (le_trans (le_add_left J I) (le_add_right (I+J) K)) (le_add_right (I+J+K) (two*V))
  have hK : Γ ⊢[PRAAx] le K G.stage :=
    le_trans (le_add_left K (I+J)) (le_add_right (I+J+K) (two*V))
  have later : Γ ⊢[PRAAx] le G.stage p :=
    source_clock_later G.stage z R B e f d h L Q S G.lower G.upper G.span
  have hr : Γ ⊢[PRAAx] le r p := le_trans
    (GaussianEulerPositivePowerChartImageSchedule.target_later r (L*R) h Q S G.lower G.upper G.span) (le_trans hI later)
  have panel := compatible_source s z R B A e f d h L Q S U M hs
  have first := GaussianEulerPowerScalingGridSchedule.original_scheduled_name_distance G.stage
    z R B A e f d h L Q S G.lower G.upper one G.span panel
  have rFirst : Γ ⊢[PRAAx] le ((Q+one)*unit τ) (unit G.stage) :=
    le_trans (query_budget (Q+one) τ) (unit_monotone hK)
  have raw := GaussianEulerPositivePowerChartImageSchedule.original_later_scheduled_ordinary_image
    r G.stage z R B A e f d h L Q S G.lower G.upper one G.span panel hI
  have reversed : Γ ⊢[PRAAx] distanceBounded u v two (unit r) :=
    distance_symmetric _ _ _ _ (unit_positive _) raw
  have scaled := GaussianEulerCompactExhaustionScaleTransport.original_scale_transport p
    z B e f d h u v two (unit r) hs.andE₁.andE₂.andE₂.andE₁ (unit_positive _) reversed
  have rSecond : Γ ⊢[PRAAx] le ((m*two)*unit τ) (unit r) :=
    le_congr (congrMul (mul_comm two m) (.eqRefl _)) (.eqRefl _) (query_budget (two*m) τ)
  have corrected := GaussianEulerPositivePowerChartImageSchedule.scheduled_corrected_source
    G.stage z R B A e f d h L Q S G.lower G.upper one G.span panel
  have cofinal := original_uniform_image_source G.cutoffIndex G.requestedStage z R B A e f d h L Q S U
    hs.andE₁ hs.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂
  have imageInput := GaussianEulerCompactExhaustionImageLattice.original_scaled_lattice_source
    r G.cutoffIndex k z R B A e f d h L Q S G.lower G.upper one G.span G.cells hs.andE₁.andE₁ corrected.andE₂ cofinal
  let x := GaussianEulerPositivePowerChartImageCuts.data k e f d h Q S G.lower G.upper one G.span G.cells
  let F := GaussianEulerPositivePowerChartImageName.latticeFactor r (L*R) h Q S G.lower G.upper
  let a := GaussianEulerPositivePowerChartImageCuts.start G.cells x F
  let W := GaussianEulerPositivePowerChartImageCuts.count G.cells x F
  let D := GaussianEulerPositivePowerChartImageCuts.denominator G.cells x F
  let H := GaussianEulerPositivePowerChartImage.reciprocalMargin h Q G.lower G.upper
  let T := GaussianEulerPositivePowerChartImageName.panelTop Q S G.lower G.upper
  have third := GaussianEulerCompactExhaustionComposition.paid_independent_image_clock τ p r q
    z R B A e f d h L Q G.cutoffIndex a W D H T imageInput (cutoff_later s z R B A e f d h L Q M hs.andE₂.andE₂)
    (le_trans hJ later) hr (query_budget (two*m) τ)
  exact GaussianEulerCompactExhaustionComposition.three_paid_comparisons (panelStage s L) q _ _ _ _
    (distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _) (le_congr (.eqRefl _) (by ipra_ring) rFirst) first)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _) (le_congr (.eqRefl _) (by ipra_ring) rSecond) scaled)
    third

private theorem combine_three (s p q a b c d : PTm n)
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

theorem original_uniform_panel_observations (s p q z R B A e f d h L Q S U M : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S U M) : Γ ⊢[PRAAx]
    distanceBounded (ap2 compactF p (compactData s z R B A e f d h L Q S U M))
      (ap2 formulaF q (formulaData z R B A e f d h L Q))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let G := grid s z R B A e f d h L Q S U M
  let x := compactData s z R B A e f d h L Q S U M
  let y := resultData z R B A e f d h L Q
  let w := formulaData z R B A e f d h L Q
  let u := s+num 3
  have native := compact_source s z R B A e f d h L Q S U M hs
  have regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN compactF x :=
    GaussianEulerPowerScalingCompactName.name_regular z R B e f d h Q S one G.span G.lower G.upper native
  have canon : Γ ⊢[PRAAx] canonical (ap2 compactF G.stage x) :=
    GaussianCompactRiemannName.name_canonical GaussianEulerPowerScalingCompactName.evaluatorF G.stage
      one G.span G.lower (GaussianEulerPowerScalingCompactRate.lipschitz R Q S G.lower G.upper) G.upper
      (GaussianEulerPowerScalingCompactName.fixedData z B e f d h S)
  have hτ : Γ ⊢[PRAAx] le (panelStage s L+two) G.imageClock := le_add_right _ _
  have hStage : Γ ⊢[PRAAx] le (panelStage s L) G.stage := by
    let j := clock (panelStage s L+two) z R B A e f d h L Q
    let v := target G.imageClock (L*R) h Q S G.lower G.upper G.span
    let K := exponent (Q+one) (panelStage s L+two)
    have hr := GaussianEulerPositivePowerChartImageSchedule.target_later (Γ := Γ)
      G.imageClock (L*R) h Q S G.lower G.upper G.span
    exact le_trans (le_add_right _ _) (le_trans hτ (le_trans hr
      (le_trans (le_add_right v j) (le_trans (le_add_right (v+j) K) (le_add_right _ _)))))
  have hp := point_at compactF x p G.stage regular
  have hLater : Γ ⊢[PRAAx] le u G.stage := le_trans (le_add_right u _) hStage
  have reduced : Γ ⊢[PRAAx] distanceBounded (ap2 compactF p x) (ap2 compactF G.stage x)
      (unit p+unit u) (unit p*unit u) := by
    have hU := unit_monotone hLater
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive _))
      (positive_product _ _ (unit_positive p) (unit_positive _)) _ hp
    ipra_le 𝔞(unit p*unit p)*sl hU
  have mid := GaussianEulerCompactExhaustionNormalization.remove_chart_coefficient_at_paid_clock
    u (panelStage s L) u (ap2 compactF G.stage x) z R B A e f d h L Q hs.andE₁.andE₁ canon
    (GaussianEulerCompactExhaustionNormalization.paid_clock u L)
    (weighted_observations s (referenceClock u L) z R B A e f d h L Q S U M hs)
  have base := GaussianEulerCompactExhaustionScaled.reference_regular z R B A e f d h L Q
    hs.andE₁.andE₁ hs.andE₁.andE₂.andE₂.andE₁
  have inv := GaussianEulerCompactExhaustionNormalization.inverse_bound e f L
    hs.andE₁.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have eq : Γ ⊢[PRAAx] crossEquivalent resultF formulaF y w :=
    GaussianBoundedConstantProductName.ordinary_product_identity referenceF L (fraction f e) _ (.andI base inv)
  exact combine_three s p q _ _ _ _ reduced mid (cross_at resultF formulaF y w u q eq)

theorem original_uniform_panel_rate (s z R B A e f d h L Q S U M : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S U M) : Γ ⊢[PRAAx]
    independentRate compactF formulaF (compactData s z R B A e f d h L Q S U M)
      (formulaData z R B A e f d h L Q) one (unit s) := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (sh z) (sh R) (sh B) (sh A) (sh e) (sh f) (sh d) (sh h) (sh L) (sh Q) (sh S) (sh U) (sh M) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,Syn.shift,subst_compactData,subst_formulaData,sh,one] using
    original_uniform_panel_observations (sh s) (var 1) (var 0) (sh z) (sh R) (sh B) (sh A)
      (sh e) (sh f) (sh d) (sh h) (sh L) (sh Q) (sh S) (sh U) (sh M) ss

theorem actual_original_uniform_power_damped_panel_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
      (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
        independentRate compactF formulaF
          (compactData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
            (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
          (formulaData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
          one (unit (var 0))) :=
  closeUniv 14 (.impI (original_uniform_panel_rate _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingUniformObservation
