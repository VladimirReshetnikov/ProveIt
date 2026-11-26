import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerPowerOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCompatibility

/-!
# The original Euler power square below time one

The actual original power is compared with the actual exponential of
the doubled coefficient (1/A-1) times the ordered harmonic logarithm.
Both genuine old-logarithm and harmonic queries are retained. This
gives the sharp lower-time signed geometry; rational-power endpoint
identification and integration of its majorant are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerPowerOrder (source inputF expF leftData rightData radius leftExpData rightExpData)
open GaussianEulerLowerPowerCoefficients (amplification)
open GaussianEulerUpperPowerCoefficients (realMultiplier)
open GaussianEulerIntegrandName (powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianEulerUpperPowerCompatibility (doubleF doubleData doubleRadius oldLogQuery squareF squareData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem old_source (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B a b := .andI h.andE₁.andE₂.andE₁.andE₁ h.andE₂.andE₁

theorem double_sample_error (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 doubleF p (doubleData z B a b)) (ap2 inputF p (leftData z R B a b))
      (two*amplification R) (unit p) := by
  let s := oldLogQuery p z B a b
  let t := GaussianBoundedConstantProductName.clock p (amplification R)
  let c := realMultiplier z B
  have sl : Γ ⊢[PRAAx] le p s := le_trans (le_add_right p (GaussianFastValueCut.normalizer two)) (le_add_right _ _)
  have tl : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have dist := GaussianEulerUpperPowerCompatibility.later_cross GaussianPositiveRationalLogarithm.logF GaussianHarmonicLogarithmName.nameF
    (GaussianPositiveRationalLogarithm.data a b) (GaussianHarmonicLogarithmName.data a b) p s t sl tl
    (GaussianHarmonicLogarithmName.cross_original a b h.andE₂.andE₁)
  have prod := GaussianNameArithmetic.product_distance c c _ _ zero two (unit p)
    (GaussianPositiveRationalLogarithm.radius a b) (amplification R) (unit_positive p)
    (GaussianRationalPowerDifference.distance_refl_zero c _ (unit_positive p)) dist
    (GaussianPositiveRationalLogarithm.sample_bound s a b h.andE₂.andE₁)
    (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁)
  exact distance_congr (GaussianEulerUpperPowerCompatibility.double_sample p z B a b).eqSymm
    (GaussianBoundedConstantProductName.sample_at GaussianHarmonicLogarithmName.nameF p (amplification R) c
      (GaussianHarmonicLogarithmName.data a b)).eqSymm (by ipra_ring) (.eqRefl _) prod

theorem double_input_cross (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    crossEquivalent doubleF inputF (doubleData z B a b) (leftData z R B a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (two*amplification R)
    (GaussianExponentialRealPart.double_real_regular _ _ (GaussianEulerIntegrandName.power_exponent_regular z B a b (old_source z R B A a b h)))
    (GaussianEulerLowerPowerOrder.product_input _ _ _ _ h.andE₂
      (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁)).andE₁
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,doubleF,doubleData,leftData,two] using
    double_sample_error (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs

theorem original_power_square (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    crossEquivalent squareF expF (squareData z B a b) (leftExpData z R B a b) := by
  have old := GaussianEulerIntegrandName.power_input z B a b (old_source z R B A a b h)
  have first := GaussianExponentialRealPart.exponential_norm_square powerExponentF (powerRadius z B a b) (powerExponentData z B a b) old
  have second := GaussianExponentialRadiusIndependence.independent_radii_proper doubleF inputF (doubleRadius z B a b) (radius R b)
    (doubleData z B a b) (leftData z R B a b) (GaussianExponentialRealPart.double_real_input _ _ _ old)
    (GaussianEulerLowerPowerOrder.product_input _ _ _ _ h.andE₂
      (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁))
    (double_input_cross z R B A a b h)
  exact cross_trans _ _ _ _ _ _ first second

/-- Actual original squared modulus has the sharp reference with the
literal coefficient (1/A-1), retaining independent observation errors. -/
theorem original_square_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.realOrder squareF expF (squareData z B a b) (rightExpData R A a b) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (original_power_square z R B A a b h)
    (GaussianNameEquivalence.cross_refl expF (rightExpData R A a b)
      (GaussianRadiusExponentialName.name_regular _ _ _
        (GaussianEulerLowerPowerOrder.product_input _ _ _ _ h.andE₂
          (GaussianEulerLowerPowerCoefficients.lower_multiplier_bound R A h.andE₁.andE₁))))
    (GaussianEulerLowerPowerOrder.ordered_exponentials z R B A a b h)

theorem original_squared_observations (p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper
      (GaussianRationalMetric.qnormSq (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF p (powerData z B a b)) (powerData z B a b)))
      (fstT (ap2 expF q (rightExpData R A a b))) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.upper_congr (GaussianEulerUpperPowerCompatibility.actual_squared_norm_sample p z B a b) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p q (original_square_order z R B A a b h))

theorem original_lower_time_power_square_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianNamedPositiveExponentialOrder.realOrder squareF expF (squareData (var 0) (var 2) (var 4) (var 5))
        (rightExpData (var 1) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_square_order _ _ _ _ _ _ Prf.hyp0))
theorem original_lower_time_actual_squared_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      RationalValueBounds.upper
        (GaussianRationalMetric.qnormSq
          (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF (var 0) (powerData (var 2) (var 4) (var 6) (var 7)))
            (powerData (var 2) (var 4) (var 6) (var 7))))
        (fstT (ap2 expF (var 1) (rightExpData (var 3) (var 5) (var 6) (var 7))))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_squared_observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerComparison
