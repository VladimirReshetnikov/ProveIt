import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartUniformRounded
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCofinalObservation

/-!
# A uniform physical cutoff schedule for the original power substitution

The fixed physical panel depends on certified magnitude bounds and on
the desired accuracy. The separately computed source and image mesh
clocks may still inspect the literal rational data.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerChartUniformEndpoints (uniform_physical_panel)
open GaussianEulerPowerChartUniformRounded (uniform_mesh_source original_uniform_rounded_panel)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize samplingIndex cutoff_guards chart_clock_budget count_positive)
open GaussianEulerPowerChartRoundedEndpoints (chartBudget)
open GaussianEulerPowerScalingGridSchedule (count imagePrecision)
open GaussianEulerPositivePowerChartCorrectedPanel (start span denominator)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPowerScalingCell (scaleBound)
open GaussianEulerCompactExhaustionNormalization (referenceClock)
open GaussianEulerCompactExhaustionScaled (cutoff cutoffGain)
open GaussianFastValueCut (exponent normalizer)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (bounded)
open GaussianRationalL1 (qL1)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalIntegerNormalization (positivePart)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def panelStage (s L : PTm n) : PTm n := referenceClock (s+num 3) L

def cutoffIndex (s A R L M : PTm n) : PTm n :=
  exponent (M*GaussianEulerCompactExhaustion.budget A R) (succ (panelStage s L+two))

@[simp] theorem subst_panelStage {m : ℕ} (σ : Fin n → PTm m) (s L : PTm n) :
    Syn.subst σ (panelStage s L) = panelStage (Syn.subst σ s) (Syn.subst σ L) := by
  simp [panelStage,referenceClock]

@[simp] theorem subst_cutoffIndex {m : ℕ} (σ : Fin n → PTm m) (s A R L M : PTm n) :
    Syn.subst σ (cutoffIndex s A R L M) =
      cutoffIndex (Syn.subst σ s) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ M) := by
  simp [cutoffIndex,GaussianEulerCompactExhaustion.budget,GaussianEulerWeightedHalfDecay.majorant]

/-- A bound on the original zero observation bounds the actual clock input. -/
theorem scale_bound_from_zero (z B e f d h U : PTm n)
    (hU : Γ ⊢[PRAAx] bounded (GaussianEulerPowerScalingCell.scaleSample zero z B e f d h) U one) :
    Γ ⊢[PRAAx] le (scaleBound z B e f d h) (two*U+two) := by
  let x := GaussianEulerPowerScalingCell.scaleSample zero z B e f d h
  let a := positivePart (numeratorOf (qL1 x))
  let b := denominatorOf (qL1 x)
  have cmp := GaussianRationalL1Algebra.qL1_of_bounded x U one (le_refl _) hU
  have cleared : Γ ⊢[PRAAx] le (one*a) ((two*U)*b) :=
    GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianGeneralFTAConstants.l1_natural_representation x)
      (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)) cmp
  have ceil := GaussianDescentClockArithmetic.ceiling_least a b (two*U)
    (RationalArgmin.denominator_positive _) (le_congr (one_mul _) (mul_comm _ _) cleared)
  exact add_le_add_right _ ceil

private theorem clock_monotone (a b s : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (exponent a s) (exponent b s) := by
  let u := GaussianRootSchedule.binaryLength a
  let v := GaussianRootSchedule.binaryLength b
  have cmp : Γ ⊢[PRAAx] le u v := by
    refine .orE (lt_or_le v u) ?_ Prf.hyp0
    have good : lt v u :: Γ ⊢[PRAAx] le a (pw two v) :=
      le_trans h.wk (GaussianRootSchedule.binary_length_correct b).andE₁
    exact .botE _ ((GaussianRootSchedule.binary_length_minimal a v Prf.hyp0).impE good)
  unfold exponent normalizer
  exact add_le_add₂ (le_refl s) (add_le_add_right two cmp)

theorem cutoff_later (s z R B A e f d h L Q M : PTm n)
    (hM : Γ ⊢[PRAAx] le (scaleBound z B e f d h) M) :
    Γ ⊢[PRAAx] le (cutoff (panelStage s L+two) z R B A e f d h L Q)
      (cutoffIndex s (Q*A) (L*R) L M) :=
  clock_monotone _ _ _ (mul_le_mul_right _ hM)

def imageSource (j s z R B A e f d h L Q S U : PTm n) : Fm PTm n :=
  let R' := L*R
  let A' := Q*A
  let V := cutoffSize j A' R'
  let E := lowerDenominator S V L
  let T := upperNumerator U V L
  let W := width L U S V
  let t := samplingIndex s V
  let N := count t z R B e f d h L Q S E T W
  let k := imagePrecision t z R B e f d h L Q S E T W N
  GaussianEulerCompactExhaustion.source (scaled z f) R' (B*e) A' j
    (start k e f d h Q S E T one W N) (span k e f d h Q S E T one W N)
    (denominator k e f d h Q S E T one W N) (reciprocalMargin h Q E T)
    (GaussianEulerPositivePowerChart.majorant Q S E T+one)

theorem original_uniform_image_source (j s z R B A e f d h L Q S U : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerChartCofinalSchedule.source z R B A e f d h L Q S)
    (hU : Γ ⊢[PRAAx] le one U) (hu : Γ ⊢[PRAAx] le h (d*U)) :
    Γ ⊢[PRAAx] imageSource j s z R B A e f d h L Q S U := by
  let R' := L*R
  let A' := Q*A
  let V := cutoffSize j A' R'
  let E := lowerDenominator S V L
  let T := upperNumerator U V L
  let W := width L U S V
  let t := samplingIndex s V
  let N := count t z R B e f d h L Q S E T W
  let k := imagePrecision t z R B e f d h L Q S E T W N
  have target := GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hs.andE₁
  have guards := cutoff_guards (Γ := Γ) j A' R'
  have inverse := le_congr (.eqRefl _) (mul_comm L e) hs.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have physical : Γ ⊢[PRAAx] GaussianEulerPowerChartUniformEndpoints.source e f d h Q S L U V :=
    .andI hs.andE₂ (.andI (.andI hs.andE₁.andE₂.andE₂.andE₂.andE₁ hU)
      (.andI (.andI inverse hu) guards.andE₁))
  have hN : Γ ⊢[PRAAx] le one N := count_positive t z R B e f d h L Q S E T W
  have hk : Γ ⊢[PRAAx] le (chartBudget N V) (unit (query k h Q E T)) :=
    chart_clock_budget s z R B e f d h L Q S E T W N V hN
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) guards.andE₁
  have small : Γ ⊢[PRAAx] le (two*N) (unit (query k h Q E T)) := by
    apply le_trans _ hk
    unfold chartBudget
    ipra_le 𝔞(two*N)*sl hV+𝔞(two*V)
  have mesh := uniform_mesh_source e f d h Q S L U V N physical hN
  have geometry := GaussianEulerPositivePowerChartCorrectedPanel.panel_geometry k e f d h Q S E T one W N (.andI mesh small)
  have contains := original_uniform_rounded_panel k e f d h Q S L U V N (etaDen j A' R') (top j A' R')
    physical hN guards.andE₂.andE₁ guards.andE₂.andE₂ hk
  have margin := GaussianEulerPositivePowerChartImage.margin_positive h Q E T hs.andE₂.andE₂.andE₁.andE₂
  exact .andI target (.andI (.andI (.andI target.andE₁.andE₂.andE₁.andE₁
    (.andI margin target.andE₁.andE₂.andE₁.andE₂)) geometry) contains)

theorem actual_original_uniform_power_chart_image_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    ((GaussianEulerPowerChartCofinalSchedule.source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
      (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ (le one (var 13) ⋏ le (var 9) (var 8*var 13))) ⟶
      imageSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 13)) :=
  closeUniv 14 (.impI (original_uniform_image_source _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformSchedule
