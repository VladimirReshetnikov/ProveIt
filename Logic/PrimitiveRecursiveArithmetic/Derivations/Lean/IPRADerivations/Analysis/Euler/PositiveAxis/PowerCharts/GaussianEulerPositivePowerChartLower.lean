import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartOrder
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealExponentialCompactLower
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalCompactObservationTightening
import IPRADerivations.Analysis.Euler.VerticalBounds.Integrands.GaussianEulerVerticalRealSamples

/-!
# A positive compact lower envelope for the genuine power chart

Every actual original real power exponent lies in its true uniform
compact disk K. The actual exponential therefore has lower envelope
3^-K, independently of all original computed input clocks. Exact
positive scaling retains the original chart observation with only its
own dyadic allowance. The numerical margin is 1/(h*3^K); no lower-value
certificate or nonzero chart output is supplied as a hypothesis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartLower

open_ipra
open GaussianEulerPositivePowerChart (source argument nameF data clock power_source)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianNamedPositiveExponentialOrder (real_order_at)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_order_left upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def exponentRadius (Q E T : PTm n) : PTm n := GaussianEulerCompactPowerMajorant.exponentRadius (Q+one) E T
def powerDenominator (Q E T : PTm n) : PTm n := pw (num 3) (exponentRadius Q E T)
def denominator (h Q E T : PTm n) : PTm n := h*powerDenominator Q E T
ipra_subst exponentRadius [GaussianEulerCompactPowerMajorant.exponentRadius, GaussianCompactLogarithmBounds.radius]
ipra_subst powerDenominator
ipra_subst denominator

theorem power_denominator_positive (Q E T : PTm n) : Γ ⊢[PRAAx] le one (powerDenominator Q E T) :=
  GaussianFactorBudget.power_positive _ _ (le_of_eq_add (d := two) (by ipra_ring))

theorem exponent_input (e f d h Q S E T a b : PTm n) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input powerExponentF (exponentRadius Q E T) (powerExponentData (argument e f) f a b) := by
  refine .andI (GaussianEulerIntegrandName.power_exponent_regular _ _ _ _ (.andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₂.andE₁)) (.allI ?_)
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h)
      (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using hs.shift
  have point := GaussianEulerCompactPowerMajorant.exponent_sample (var 0) (argument (Syn.shift e) (Syn.shift f))
    (Syn.shift Q+one) (Syn.shift f) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b)
    (power_source _ _ _ _ _ _ _ _ _ _ ss) ss.andE₂.andE₂
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,GaussianEulerIntegrandName.subst_powerExponentData,
    GaussianEulerPositivePowerChart.subst_argument,subst_exponentRadius,exponentRadius,
    GaussianEulerCompactPowerMajorant.exponentRadius,GaussianCompactLogarithmBounds.radius,PTm.subst_add,PTm.subst_mul,
    GaussianCompactLogarithmBounds.subst_radius,PTm.subst_num,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using point

theorem exponent_real_samples (e f a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) : Γ ⊢[PRAAx]
    realSamples powerExponentF (powerExponentData (argument e f) f a b) := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift f) := by simpa [Fm.shift,Syn.shift,one] using hf.shift
  let z := argument (Syn.shift e) (Syn.shift f)
  let B := Syn.shift f
  let A := Syn.shift a
  let D := Syn.shift b
  let t := GaussianEulerIntegrandName.powerClock (var 0) z B A D
  have caxis := RationalGaussianEmbedding.axis_congr
    (GaussianEulerPositivePowerChart.coefficient_exact (Syn.shift e) B fs).eqSymm
    (GaussianEulerPositivePowerChartOrder.fraction_positive (Syn.shift e) B fs).andE₁
  have read := GaussianEulerIntegrandName.power_exponent_at (Γ := Γ.map Fm.shift) (var 0) z B A D
  have r := Prf.andI (GaussianRationalHorner.canonical_congr read (GaussianRationalHorner.qmul_canonical _ _))
    (RationalGaussianEmbedding.axis_congr read.eqSymm
      (RationalGaussianEmbedding.axis_multiply _ _ caxis (GaussianPositiveRationalLogarithm.sample_axis t A D)))
  simpa only [realSamples,Syn.shift,GaussianEulerIntegrandName.subst_powerExponentData,
    GaussianEulerPositivePowerChart.subst_argument,z,B,A,D] using r

/-- The exact original chart outputs are canonical real rational codes. -/
theorem original_sample_real (p e f d h S a b : PTm n)
    (hf : Γ ⊢[PRAAx] le one f) (hh : Γ ⊢[PRAAx] le one h) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 nameF p (data e f d h S a b)) ⋏
      RationalGaussianEmbedding.axis (ap2 nameF p (data e f d h S a b)) := by
  have powerReal := GaussianEulerVerticalRealSamples.original_exponential_real_at powerExponentF (powerRadius (argument e f) f a b)
    (powerExponentData (argument e f) f a b) (clock p S) (exponent_real_samples e f a b hf)
  have scaleReal := (GaussianEulerPositivePowerChartOrder.fraction_positive (Γ := Γ) d h hh).andE₁
  have read := GaussianEulerPositivePowerChart.sample_at (Γ := Γ) p e f d h S a b
  exact .andI (GaussianRationalHorner.canonical_congr read (GaussianRationalHorner.qmul_canonical _ _))
    (RationalGaussianEmbedding.axis_congr read.eqSymm (RationalGaussianEmbedding.axis_multiply _ _ scaleReal powerReal.andE₂))

theorem original_power_lower (p e f d h Q S E T a b : PTm n) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    upper (fraction one (powerDenominator Q E T)) (fstT (ap2 powerF p (powerData (argument e f) f a b))) one (unit p) := by
  let K := exponentRadius Q E T
  let X := powerExponentData (argument e f) f a b
  let R := powerRadius (argument e f) f a b
  let c := fraction (one : PTm n) (powerDenominator Q E T)
  let y := fstT (ap2 powerF p (powerData (argument e f) f a b))
  let t := GaussianNamedRealOrderTransport.precision c y (unit p) two
  have hi := exponent_input e f d h Q S E T a b hs
  have hr := exponent_real_samples e f a b hs.andE₁.andE₁.andE₂
  have old := GaussianEulerIntegrandName.power_input (argument e f) f a b (.andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₂.andE₁)
  have cross := GaussianExponentialRadiusIndependence.same_input_cross powerExponentF K R X hi old
  have lower := GaussianRealExponentialCompactLower.original_observation_lower powerExponentF t K X hi hr
  have near := GaussianNameEquivalence.cross_at _ _ _ _ t p cross
  have scalar := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p)) near)
  have joined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ lower scalar
  have budget : Γ ⊢[PRAAx] GaussianNamedRealOrderTransport.upperSlack c y one (unit p) two t :=
    RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t)
      (positive_product _ _ (unit_positive t) (unit_positive p))) joined (le_of_eq_add (d := zero) (by ipra_ring))
  exact GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ two budget

/-- Exact source-only lower envelope at the unchanged actual chart query. -/
theorem original_observation_lower (p e f d h Q S E T a b : PTm n) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    upper (fraction one (denominator h Q E T)) (fstT (ap2 nameF p (data e f d h S a b))) one (unit p) := by
  let M := powerDenominator Q E T
  let u := clock p S
  let x := GaussianPositiveRationalLogarithm.fraction one M
  let y := ap2 powerF u (powerData (argument e f) f a b)
  let c := GaussianPositiveRationalLogarithm.fraction d h
  have hh := hs.andE₁.andE₂.andE₁.andE₂
  have hd := hs.andE₁.andE₂.andE₁.andE₁
  have hM := power_denominator_positive (Γ := Γ) Q E T
  have px := GaussianEulerDecayFactorBounds.fraction_is_radius_point one M hM
  have repx := GaussianRationalHorner.scalar_congr (congrFst px).eqSymm (ZT.derive rfl) (.eqRefl _)
    (GaussianPositiveExponentialOrder.radius_real_representation one M hM)
  have small : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT x) (fraction one M) :=
    GaussianRationalMetric.comparison_of_cleared _ _ one one M M hM hM repx (fraction_represents one M hM) (le_of_eq_add (d := zero) (by ipra_ring))
  have lower := upper_order_left _ _ _ _ _ small (original_power_lower u e f d h Q S E T a b hs)
  have scaled := GaussianEulerPositivePowerChartOrder.scale_upper d h x y one (unit u) hh lower
  have factor := GaussianEulerDampedTimeRate.fraction_product d h one M hh hM
  have productRep := GaussianRationalHorner.scalar_congr (congrFst factor).eqSymm (ZT.derive rfl) (.eqRefl _)
    (GaussianRationalHorner.scalar_congr
      (congrFst (GaussianEulerDecayFactorBounds.fraction_is_radius_point (d*one) (h*M) (positive_product _ _ hh hM))).eqSymm
      (ZT.derive rfl) (.eqRefl _) (GaussianPositiveExponentialOrder.radius_real_representation (d*one) (h*M) (positive_product _ _ hh hM)))
  have leading : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fraction one (h*M)) (fstT (GaussianRationalHorner.qmul c x)) :=
    GaussianRationalMetric.comparison_of_cleared _ _ one (d*one) (h*M) (h*M) (positive_product _ _ hh hM) (positive_product _ _ hh hM)
      (fraction_represents one (h*M) (positive_product _ _ hh hM)) productRep
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (h*M) hd))
  have scaledLower := upper_order_left _ _ _ _ _ leading scaled
  have clockBudget : Γ ⊢[PRAAx] le (S*unit p) (unit u) := GaussianFastValueCut.query_budget S p
  have error := RationalValueBounds.upper_mono _ _ _ _ one (unit p) (positive_product _ _ hh (unit_positive u)) scaledLower (by
    ipra_le 𝔞 h*sl clockBudget+𝔞 (unit p)*sl hs.andE₁.andE₂.andE₂.andE₂.andE₂)
  exact upper_congr (.eqRefl _) (congrFst (GaussianEulerPositivePowerChart.sample_at p e f d h S a b)).eqSymm (.eqRefl _) (.eqRefl _) error

/-- Actual sufficiently late rational chart samples have an exact positive
real margin. This is a numerical query guard, not a value assumption. -/
theorem original_positive_sample (p e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b)
    (hp : Γ ⊢[PRAAx] le (two*denominator h Q E T) (unit p)) : Γ ⊢[PRAAx]
    upper (fraction one (two*denominator h Q E T)) (fstT (ap2 nameF p (data e f d h S a b))) zero one :=
  RationalCompactObservationTightening.lower_guard _ (denominator h Q E T) (two*denominator h Q E T) (unit p)
    (positive_product _ _ hs.andE₁.andE₂.andE₁.andE₂ (power_denominator_positive Q E T)) (le_refl _) hp
    (original_observation_lower p e f d h Q S E T a b hs)

theorem actual_original_positive_power_chart_compact_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      upper (fraction one (denominator (var 4) (var 5) (var 7) (var 8)))
        (fstT (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 6) (var 9) (var 10)))) one (unit (var 0))) :=
  closeUniv 11 (.impI (original_observation_lower _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartLower
