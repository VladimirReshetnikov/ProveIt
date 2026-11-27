import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChart
import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerIncrement
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate

/-!
# Evaluated Jacobian and exact first-order step of the positive power chart

The actual chart uses the original power evaluator. Its Jacobian is the
computed chart observation multiplied by e*b/(f*a), exactly r*chart(t)/t.
The finite linear term is EXACTLY that Jacobian times step/b. Only the
quadratic error uses the loose compact disk Q+1. The two original chart
queries remain independent, with errors 2^-p+5*2^-q.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartJacobian

open_ipra
open GaussianEulerPositivePowerChart (argument parameters nameF data clock coefficient_exact power_source scale_bound sample_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (qsub distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactLogarithmBounds (domain)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (e f d h Q S E T a b step : PTm n) : Fm PTm n :=
  GaussianEulerPositivePowerChart.source e f d h Q S E T a b ⋏
    (domain (a+step) b E T ⋏ le (((Q+one)+one)*step) a)
def point (p e f d h S a b : PTm n) : PTm n := ap2 nameF p (data e f d h S a b)
def jacobian (p e f d h S a b : PTm n) : PTm n := qmul (point p e f d h S a b) (fraction (e*b) (f*a))
def increment (p q e f d h S a b step : PTm n) : PTm n :=
  qsub (point p e f d h S (a+step) b) (point q e f d h S a b)
def linearTerm (q e f d h S a b step : PTm n) : PTm n :=
  qmul (point q e f d h S a b) (fraction (e*step) (f*a))
def curvature (Q S E T step : PTm n) : PTm n := S*GaussianEulerPowerIncrement.curvature (Q+one) E T step
def numerator (p q Q S E T b step : PTm n) : PTm n :=
  (E*E)*curvature Q S E T step*(unit p*unit q)+(unit q+num 5*unit p)*(b*b)
def denominator (p q b : PTm n) : PTm n := (b*b)*(unit p*unit q)

ipra_subst source
ipra_subst point
ipra_subst jacobian
ipra_subst increment
ipra_subst linearTerm
ipra_subst curvature [GaussianEulerPowerIncrement.curvature, GaussianEulerPowerIncrement.productRemainder, GaussianEulerPowerExponentialShift.coefficient, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius, GaussianCompactLogarithmBounds.radius]
ipra_subst numerator
ipra_subst denominator

theorem original_power_source (e f d h Q S E T a b step : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b step) : Γ ⊢[PRAAx]
    GaussianEulerPowerShiftRate.source (argument e f) (Q+one) f E T a b step :=
  .andI (power_source e f d h Q S E T a b hs.andE₁)
    (.andI hs.andE₁.andE₂.andE₂ hs.andE₂)

theorem original_linear_factor (e f a step : PTm n) (hf : Γ ⊢[PRAAx] le one f)
    (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx]
    GaussianEulerPowerExponentIncrement.linear (argument e f) f a step ≐ fraction (e*step) (f*a) :=
  (qmul_congr (coefficient_exact e f hf) (.eqRefl _)).eqTrans (fraction_product e f step a hf ha)

theorem fraction_congr {a b c d : PTm n} (hA : Γ ⊢[PRAAx] a ≐ c) (hB : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx]
    fraction a b ≐ fraction c d :=
  GaussianRationalHorner.real_fraction_congr hA hB

/-- Genuine canonical rational cancellation, including a zero numerator. -/
theorem fraction_cancel (a b t : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le one t) : Γ ⊢[PRAAx]
    fraction (a*t) (b*t) ≐ fraction a b := by
  have hd := positive_product b t hb ht
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.scale t (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode))
      (ComplexLogarithmRemainder.scale (a*t) ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
      ipra_simps <;> ring
  have rep := GaussianRationalHorner.represents_rescale (fraction a b)
    (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b t
    (GaussianRationalHorner.ofGaussian_represents _ _ hb)
  exact GaussianRationalHorner.canonical_unique _ _ _ _
    (GaussianRationalHorner.ofGaussian_canonical _ _ hd) (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hd
    (GaussianRationalHorner.ofGaussian_represents _ _ hd)
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _) rep)

/-- The computed Jacobian multiplied by the physical step is the exact
linear term, with the original earlier chart query unchanged. -/
theorem jacobian_step (q e f d h S a b step : PTm n)
    (hf : Γ ⊢[PRAAx] le one f) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qmul (jacobian q e f d h S a b) (fraction step b) ≐ linearTerm q e f d h S a b step := by
  have factor : Γ ⊢[PRAAx] qmul (fraction (e*b) (f*a)) (fraction step b) ≐ fraction (e*step) (f*a) :=
    (fraction_product (e*b) (f*a) step b (positive_product f a hf ha) hb).eqTrans
      ((fraction_congr (by ipra_ring) (.eqRefl _)).eqTrans (fraction_cancel (e*step) (f*a) b (positive_product _ _ hf ha) hb))
  exact (GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans (qmul_congr (.eqRefl _) factor)

/-- Every actual Jacobian observation is uniformly bounded on the source compact. -/
theorem jacobian_bound (q e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    bounded (jacobian q e f d h S a b) (GaussianEulerPositivePowerChart.majorant Q S E T*(Q*E)) one := by
  have hf := hs.andE₁.andE₁.andE₂
  have ha := hs.andE₂.andE₂.andE₁.andE₁
  have exponent := hs.andE₁.andE₂.andE₂.andE₂.andE₁
  have lowerTime := hs.andE₂.andE₂.andE₂.andE₁
  have upper : Γ ⊢[PRAAx] le (e*b) ((Q*E)*(f*a)) := by
    ipra_le 𝔞 b*sl exponent+𝔞 Q*𝔞 f*sl lowerTime
  have factor := GaussianEulerExponentCompactBounds.fraction_bound (e*b) (f*a) (Q*E) (positive_product _ _ hf ha) upper
  exact GaussianRationalReciprocal.bounded_product_one (GaussianEulerPositivePowerChart.original_bound q e f d h Q S E T a b hs) factor

/-- Scaling transports the genuine original increment before any clock coarsening. -/
theorem original_retimed_increment (p q e f d h Q S E T a b step : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b step) : Γ ⊢[PRAAx]
    distanceBounded (increment p q e f d h S a b step) (linearTerm q e f d h S a b step)
      (S*GaussianEulerPowerIncrement.compactNumerator (clock p S) (clock q S) (Q+one) E T b step)
      (GaussianEulerPowerIncrement.remainderDenominator (clock p S) (clock q S) b) := by
  let U := clock p S
  let V := clock q S
  let oldX := GaussianEulerPowerIncrement.point U (argument e f) f (a+step) b
  let oldY := GaussianEulerPowerIncrement.point V (argument e f) f a b
  let oldL := GaussianEulerPowerExponentIncrement.linear (argument e f) f a step
  let c := fraction d h
  let A := GaussianEulerPowerIncrement.compactNumerator U V (Q+one) E T b step
  let D := GaussianEulerPowerIncrement.remainderDenominator U V b
  have hf := hs.andE₁.andE₁.andE₁.andE₂
  have ha := hs.andE₁.andE₂.andE₂.andE₁.andE₁
  have hb := hs.andE₁.andE₂.andE₂.andE₁.andE₂
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hb hb)
    (positive_product _ _ (unit_positive U) (unit_positive V))
  have old := GaussianEulerPowerIncrement.compact_power_increment U V (argument e f) (Q+one) f E T a b step
    (original_power_source e f d h Q S E T a b step hs)
  have lift := GaussianApproximateInverseDistance.multiply_distance c (qsub oldX oldY) (qmul oldY oldL) S A D hD
    (scale_bound e f d h Q S hs.andE₁.andE₁) old
  have left : Γ ⊢[PRAAx] increment p q e f d h S a b step ≐ qmul c (qsub oldX oldY) :=
    (GaussianRationalSyntheticDivision.qsub_congr (sample_at p e f d h S (a+step) b) (sample_at q e f d h S a b)).eqTrans
      (GaussianRationalRoundedPower.multiplication_difference c oldX oldY)
  have right : Γ ⊢[PRAAx] linearTerm q e f d h S a b step ≐ qmul c (qmul oldY oldL) :=
    (qmul_congr (sample_at q e f d h S a b) (original_linear_factor e f a step hf ha).eqSymm).eqTrans
      (GaussianReciprocalHorner.qmul_associative c oldY oldL)
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) lift

theorem original_increment (p q e f d h Q S E T a b step : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b step) : Γ ⊢[PRAAx]
    distanceBounded (increment p q e f d h S a b step) (linearTerm q e f d h S a b step)
      (numerator p q Q S E T b step) (denominator p q b) := by
  let P := unit p
  let Qr := unit q
  let U := unit (clock p S)
  let V := unit (clock q S)
  let A := GaussianEulerPowerIncrement.compactNumerator (clock p S) (clock q S) (Q+one) E T b step
  let D := GaussianEulerPowerIncrement.remainderDenominator (clock p S) (clock q S) b
  have hb := hs.andE₁.andE₂.andE₂.andE₁.andE₂
  have bP : Γ ⊢[PRAAx] le (S*P) U := GaussianFastValueCut.query_budget S p
  have bQ : Γ ⊢[PRAAx] le (S*Qr) V := GaussianFastValueCut.query_budget S q
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hb hb)
    (positive_product _ _ (unit_positive (clock p S)) (unit_positive (clock q S)))
  have hn : Γ ⊢[PRAAx] le one (denominator p q b) := positive_product _ _ (positive_product _ _ hb hb)
    (positive_product _ _ (unit_positive p) (unit_positive q))
  exact distance_radius_mono _ _ _ _ _ _ hd hn
    (by dsimp only [A,D]
        unfold numerator denominator curvature GaussianEulerPowerIncrement.compactNumerator GaussianEulerPowerIncrement.remainderDenominator
        dsimp only [P,Qr,U,V] at bP bQ ⊢
        ipra_le (𝔞 b*𝔞 b*𝔞 b*𝔞 b*𝔞 (unit q)*𝔞 (unit (clock q S)))*sl bP+
          (5*𝔞 b*𝔞 b*𝔞 b*𝔞 b*𝔞 (unit p)*𝔞 (unit (clock p S)))*sl bQ)
    (original_retimed_increment p q e f d h Q S E T a b step hs)

/-- The actual numerical Jacobian program, with no new oracle or recursor. -/
def jacobianF : PR 8 := PTm.toPR (jacobian (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p e f d h S a b : PTm n) : PTm n := PTm.app jacobianF ![p,e,f,d,h,S,a,b]
ipra_subst run

theorem program_at (p e f d h S a b : PTm n) : Γ ⊢[PRAAx] run p e f d h S a b ≐ jacobian p e f d h S a b := by
  have decoded : Syn.subst ![p,e,f,d,h,S,a,b]
      (jacobian (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) = jacobian p e f d h S a b := by
    simp only [subst_jacobian,Syn.subst_var]
    rfl
  simpa only [run,jacobianF,decoded] using
    toPR_eq (Γ := Γ) (jacobian (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,e,f,d,h,S,a,b]

theorem original_jacobian_increment (p q e f d h Q S E T a b step : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b step) : Γ ⊢[PRAAx]
    distanceBounded (increment p q e f d h S a b step) (qmul (run q e f d h S a b) (fraction step b))
      (numerator p q Q S E T b step) (denominator p q b) :=
  distance_congr (.eqRefl _)
    ((qmul_congr (program_at q e f d h S a b) (.eqRefl _)).eqTrans
      (jacobian_step q e f d h S a b step hs.andE₁.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₂.andE₁.andE₁ hs.andE₁.andE₂.andE₂.andE₁.andE₂)).eqSymm
    (.eqRefl _) (.eqRefl _) (original_increment p q e f d h Q S E T a b step hs)

theorem actual_positive_power_chart_first_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      distanceBounded (increment (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11) (var 12))
        (linearTerm (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11) (var 12))
        (numerator (var 0) (var 1) (var 6) (var 7) (var 8) (var 9) (var 11) (var 12))
        (denominator (var 0) (var 1) (var 11))) :=
  closeUniv 13 (.impI (original_increment _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_evaluated_positive_power_Jacobian_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      distanceBounded (increment (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11) (var 12))
        (qmul (run (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11)) (fraction (var 12) (var 11)))
        (numerator (var 0) (var 1) (var 6) (var 7) (var 8) (var 9) (var 11) (var 12))
        (denominator (var 0) (var 1) (var 11))) :=
  closeUniv 13 (.impI (original_jacobian_increment _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartJacobian
