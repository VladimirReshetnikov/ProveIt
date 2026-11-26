import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerOrder
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntegerExponential

/-!
# The ordered arguments are the original Euler power square and rational power

The left input is identified with the actual conjugate sum of the old
logarithm product by its genuine two observation clocks. The right input
is the actual integer logarithm product. Independent-radius exponential
properness preserves both original programs and their original data.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerCompatibility

open_ipra
open GaussianEulerUpperPowerOrder (source leftData rightData radius leftExpData rightExpData inputF expF)
open GaussianEulerUpperPowerCoefficients (realMultiplier upperMultiplier amplification)
open GaussianEulerIntegrandName (coefficient powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianRationalHorner (qmul qadd)
open GaussianRationalConjugation (point)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def doubleData (z B a b : PTm n) : PTm n := GaussianExponentialRealPart.doubleRealData (powerExponentData z B a b)
def doubleRadius (z B a b : PTm n) : PTm n := powerRadius z B a b+powerRadius z B a b
def doubleF : PR 2 := GaussianExponentialRealPart.doubleRealF powerExponentF
def oldLogQuery (p z B a b : PTm n) : PTm n :=
  GaussianEulerIntegrandName.powerClock (GaussianFastValueCut.exponent two p) z B a b
def squareF : PR 2 := GaussianExponentialRealPart.squareF powerF
def squareData (z B a b : PTm n) : PTm n := GaussianExponentialRealPart.squareData powerF (powerData z B a b)
ipra_subst doubleData
ipra_subst doubleRadius
ipra_subst oldLogQuery
ipra_subst squareData

theorem old_source (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B a b := .andI h.andE₁.andE₁ h.andE₂.andE₁

theorem conjugate_real_product (c l : PTm n)
    (hl : Γ ⊢[PRAAx] GaussianRationalHorner.canonical l ⋏ RationalGaussianEmbedding.axis l) : Γ ⊢[PRAAx]
    qadd (qmul c l) (point (qmul c l)) ≐ qmul (qadd c (point c)) l := by
  have e := RationalGaussianEmbedding.canonical_axis_roundtrip (Γ := Γ) l hl.andE₁ hl.andE₂
  have fixed := (GaussianRationalConjugation.point_congr e.eqSymm).eqTrans
    ((GaussianRationalConjugation.point_embed _).eqTrans e)
  have left := GaussianRationalSyntheticDivision.qadd_congr (.eqRefl (qmul c l))
    ((GaussianRationalConjugation.point_mul c l).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) fixed))
  have right := (GaussianRationalPowerAlgebra.qmul_commutative (Γ := Γ) (qadd c (point c)) l).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add l c (point c)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
        (GaussianRationalPowerAlgebra.qmul_commutative _ _)))
  exact left.eqTrans right.eqSymm

theorem double_sample (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 doubleF p (doubleData z B a b) ≐ qmul (realMultiplier z B)
      (GaussianPositiveRationalLogarithm.sample (oldLogQuery p z B a b) a b) := by
  let v := ap2 powerExponentF (GaussianFastValueCut.exponent two p) (powerExponentData z B a b)
  have e := (GaussianExponentialRealPart.double_real_sample (Γ := Γ) powerExponentF p (powerExponentData z B a b)).eqTrans
    (GaussianExponentialRealPart.conjugate_sum v).eqSymm
  have old := GaussianEulerIntegrandName.power_exponent_at (Γ := Γ) (GaussianFastValueCut.exponent two p) z B a b
  exact e.eqTrans ((GaussianRationalSyntheticDivision.qadd_congr old (GaussianRationalConjugation.point_congr old)).eqTrans
    (conjugate_real_product _ _ (.andI (GaussianPositiveRationalLogarithm.sample_canonical _ a b)
      (GaussianPositiveRationalLogarithm.sample_axis _ a b))))

theorem later_cross (f g : PR 2) (x y p s t : PTm n) (hs : Γ ⊢[PRAAx] le p s) (ht : Γ ⊢[PRAAx] le p t)
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (ap2 g t y) two (unit p) :=
  GaussianRationalDistanceOrder.distance_two_errors _ _ _ _ _
    (unit_positive s) (unit_positive t) (unit_positive p)
    (GaussianExponentialReference.unit_monotone hs) (GaussianExponentialReference.unit_monotone ht)
    (GaussianNameEquivalence.cross_at f g x y s t h)

private abbrev harmonicProductData (M z B a b : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data M (realMultiplier z B) (GaussianHarmonicLogarithmName.data a b)

/-- The original doubled power input agrees with the harmonic product at its supplied multiplier bound. -/
theorem double_sample_error_of_bound (p z B a b M : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hM : Γ ⊢[PRAAx] bounded (realMultiplier z B) M one) : Γ ⊢[PRAAx]
    distanceBounded (ap2 doubleF p (doubleData z B a b)) (ap2 inputF p (harmonicProductData M z B a b))
      (two*M) (unit p) := by
  let s := oldLogQuery p z B a b
  let t := GaussianBoundedConstantProductName.clock p M
  let c := realMultiplier z B
  have sl : Γ ⊢[PRAAx] le p s := le_trans (le_add_right p (GaussianFastValueCut.normalizer two))
    (le_add_right _ _)
  have tl : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have dist := later_cross GaussianPositiveRationalLogarithm.logF GaussianHarmonicLogarithmName.nameF
    (GaussianPositiveRationalLogarithm.data a b) (GaussianHarmonicLogarithmName.data a b) p s t sl tl
    (GaussianHarmonicLogarithmName.cross_original a b h)
  have prod := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference c _ _).eqSymm (mul_comm M two) (one_mul _)
    (GaussianRationalReciprocal.bounded_product c _ M one two (unit p) (le_refl one) (unit_positive p) hM dist)
  exact distance_congr (double_sample p z B a b).eqSymm
    (GaussianBoundedConstantProductName.sample_at GaussianHarmonicLogarithmName.nameF p M c
      (GaussianHarmonicLogarithmName.data a b)).eqSymm (.eqRefl _) (.eqRefl _) prod

theorem double_sample_error (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 doubleF p (doubleData z B a b)) (ap2 inputF p (leftData z R B a b))
      (two*amplification R) (unit p) :=
  double_sample_error_of_bound p z B a b (amplification R) h.andE₂.andE₁
    (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁)

theorem double_input_cross_of_bound (z B a b M : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b)
    (hM : Γ ⊢[PRAAx] bounded (realMultiplier z B) M one) : Γ ⊢[PRAAx]
    crossEquivalent doubleF inputF (doubleData z B a b) (harmonicProductData M z B a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (two*M)
    (GaussianExponentialRealPart.double_real_regular _ _ (GaussianEulerIntegrandName.power_exponent_regular z B a b h))
    (GaussianBoundedConstantProductName.name_regular _ _ _ _
      (.andI (GaussianHarmonicLogarithmName.name_regular a b h.andE₂) hM))
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (sh a) (sh b) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.andE₂.shift
  have hMs : Γ.map Fm.shift ⊢[PRAAx] bounded (realMultiplier (sh z) (sh B)) (sh M) one :=
    by simpa [Fm.shift,Syn.shift,sh] using hM.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,doubleF,doubleData,harmonicProductData,two,sh] using
    double_sample_error_of_bound (var 0) (sh z) (sh B) (sh a) (sh b) (sh M) hs hMs

theorem double_input_cross (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent doubleF inputF (doubleData z B a b) (leftData z R B a b) :=
  double_input_cross_of_bound z B a b (amplification R) (old_source z R B a b h)
    (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁)

theorem original_power_square_of_input (z B a b M U : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b)
    (hM : Γ ⊢[PRAAx] bounded (realMultiplier z B) M one)
    (hInput : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input inputF U (harmonicProductData M z B a b)) : Γ ⊢[PRAAx]
    crossEquivalent squareF expF (squareData z B a b)
      (GaussianRadiusExponentialName.data U (harmonicProductData M z B a b)) := by
  let x := harmonicProductData M z B a b
  have old := GaussianEulerIntegrandName.power_input z B a b h
  have first := GaussianExponentialRealPart.exponential_norm_square powerExponentF (powerRadius z B a b) (powerExponentData z B a b) old
  have second := GaussianExponentialRadiusIndependence.independent_radii_proper doubleF inputF (doubleRadius z B a b) U
    (doubleData z B a b) x (GaussianExponentialRealPart.double_real_input _ _ _ old) hInput
    (double_input_cross_of_bound z B a b M h hM)
  exact cross_trans _ _ _ _ _ _ first second

theorem original_power_square (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent squareF expF (squareData z B a b) (leftExpData z R B a b) := by
  have hM := GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁
  exact original_power_square_of_input z B a b (amplification R) (radius R a) (old_source z R B a b h) hM
    (GaussianEulerUpperPowerOrder.product_input _ _ _ _ h.andE₂ hM)

theorem right_integer_input (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent inputF GaussianHarmonicIntegerExponential.originalExponentF (rightData R a b)
      (GaussianHarmonicIntegerExponential.originalExponentData (two*R) a b) := by
  let C := upperMultiplier R
  let H := GaussianHarmonicLogarithmName.nameF
  let X := GaussianHarmonicLogarithmName.data a b
  let Y := GaussianPositiveRationalLogarithm.data a b
  have first := GaussianBoundedConstantProductName.ordinary_product_identity H (amplification R) C X
    (.andI (GaussianHarmonicLogarithmName.name_regular a b h.andE₂.andE₁)
      (GaussianEulerUpperPowerCoefficients.upper_multiplier_bound R))
  have second := GaussianNameArithmetic.multiply_equivalent GaussianGammaCanonicalExponent.constantF GaussianGammaCanonicalExponent.constantF
    H GaussianPositiveRationalLogarithm.logF C C X Y
    (GaussianGammaCanonicalExponent.constant_regular C) (GaussianGammaCanonicalExponent.constant_regular C)
    (GaussianHarmonicLogarithmName.name_regular a b h.andE₂.andE₁) (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂.andE₁)
    (GaussianNameEquivalence.diagonal_refl _ C)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b h.andE₂.andE₁)))
  exact cross_trans _ _ _ _ _ _ first second

theorem original_rational_power (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent expF GaussianGammaCanonicalExponent.constantF (rightExpData R a b)
      (GaussianHarmonicIntegerExponential.rationalPower a b (two*R)) := by
  have time : Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b one a :=
    .andI (le_refl one) (GaussianEulerUpperPowerOrder.actual_time_domain a b h.andE₂)
  have target := GaussianGammaFiniteApproximantName.exponential_input GaussianHarmonicIntegerExponential.originalExponentF
    (GaussianHarmonicIntegerExponential.originalExponentData (two*R) a b)
    (GaussianHarmonicIntegerExponential.original_exponent_regular (two*R) a b one a time)
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper inputF GaussianHarmonicIntegerExponential.originalExponentF
    (radius R a) (GaussianHarmonicIntegerExponential.originalRadius (two*R) a b) (rightData R a b)
    (GaussianHarmonicIntegerExponential.originalExponentData (two*R) a b)
    (GaussianEulerUpperPowerOrder.product_input _ _ _ _ h.andE₂ (GaussianEulerUpperPowerCoefficients.upper_multiplier_bound R)) target
    (right_integer_input z R B a b h)
  exact cross_trans _ _ _ _ _ _ proper (GaussianHarmonicIntegerExponential.original_integer_exponential (two*R) a b one a time)

theorem original_square_order (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.realOrder squareF GaussianGammaCanonicalExponent.constantF
      (squareData z B a b) (GaussianHarmonicIntegerExponential.rationalPower a b (two*R)) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (original_power_square z R B a b h)
    (original_rational_power z R B a b h) (GaussianEulerUpperPowerOrder.ordered_exponentials z R B a b h)

theorem upper_budget (p t z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (ap2 squareF p (squareData z B a b)))
      (RationalNonnegativePowers.power a b (two*R)) one (unit p) one t := by
  have order := GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p t (original_square_order z R B a b h)
  have right := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) t
    (GaussianHarmonicIntegerExponential.rationalPower a b (two*R)))).eqTrans
      ((fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _
        (RationalNonnegativePowers.power_canonical a b (two*R) h.andE₂.andE₁.andE₂)))
  exact RationalValueBounds.upper_congr (.eqRefl _) right (by ipra_ring) (.eqRefl _) order

theorem square_observation_upper (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (ap2 squareF p (squareData z B a b)))
      (RationalNonnegativePowers.power a b (two*R)) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ one
    (upper_budget p (GaussianNamedRealOrderTransport.precision (fstT (ap2 squareF p (squareData z B a b)))
      (RationalNonnegativePowers.power a b (two*R)) (unit p) one) z R B a b h)

theorem actual_squared_norm_sample (p z B a b : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 squareF p (squareData z B a b)) ≐ GaussianRationalMetric.qnormSq
      (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF p (powerData z B a b)) (powerData z B a b)) :=
  (congrFst (GaussianExponentialRealPart.square_sample powerF p (powerData z B a b))).eqTrans
    ((fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _ (GaussianRationalMetric.qnormSq_canonical _)))

/-- The unchanged original Euler power is bounded at its actual square
product clock by t^(2R)+2^-p, under only the native disk and t>=1. -/
theorem original_power_squared_upper (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper
      (GaussianRationalMetric.qnormSq
        (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF p (powerData z B a b)) (powerData z B a b)))
      (RationalNonnegativePowers.power a b (two*R)) one (unit p) :=
  RationalValueBounds.upper_congr (actual_squared_norm_sample p z B a b) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (square_observation_upper p z R B a b h)

theorem original_Euler_power_square_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ crossEquivalent squareF expF
      (squareData (var 0) (var 2) (var 3) (var 4)) (leftExpData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_power_square _ _ _ _ _ Prf.hyp0))
theorem original_integer_upper_power_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ crossEquivalent expF GaussianGammaCanonicalExponent.constantF
      (rightExpData (var 1) (var 3) (var 4)) (GaussianHarmonicIntegerExponential.rationalPower (var 3) (var 4) (two*var 1))) :=
  closeUniv 5 (.impI (original_rational_power _ _ _ _ _ Prf.hyp0))

theorem original_upper_tail_actual_power_squared_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalValueBounds.upper
        (GaussianRationalMetric.qnormSq
          (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF (var 0) (powerData (var 1) (var 3) (var 4) (var 5)))
            (powerData (var 1) (var 3) (var 4) (var 5))))
        (RationalNonnegativePowers.power (var 4) (var 5) (two*var 2)) one (unit (var 0))) :=
  closeUniv 6 (.impI (original_power_squared_upper _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperPowerCompatibility
