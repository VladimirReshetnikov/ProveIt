import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperPowerOrder
import IPRADerivations.Analysis.Euler.GaussianHarmonicIntegerExponential

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerOrder (source leftData rightData radius leftExpData rightExpData inputF expF)
open GaussianEulerUpperPowerCoefficients (realMultiplier upperMultiplier amplification)
open GaussianEulerIntegrandName (coefficient powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianRationalHorner (qmul qadd)
open GaussianRationalConjugation (point)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def doubleData (z B a b : PTm n) : PTm n := GaussianExponentialRealPart.doubleRealData (powerExponentData z B a b)
def doubleRadius (z B a b : PTm n) : PTm n := powerRadius z B a b+powerRadius z B a b
def doubleF : PR 2 := GaussianExponentialRealPart.doubleRealF powerExponentF
def oldLogQuery (p z B a b : PTm n) : PTm n :=
  GaussianEulerIntegrandName.powerClock (GaussianFastValueCut.exponent two p) z B a b
def squareF : PR 2 := GaussianExponentialRealPart.squareF powerF
def squareData (z B a b : PTm n) : PTm n := GaussianExponentialRealPart.squareData powerF (powerData z B a b)
@[simp] theorem subst_doubleData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (doubleData z B a b) = doubleData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [doubleData]
@[simp] theorem subst_doubleRadius {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (doubleRadius z B a b) = doubleRadius (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [doubleRadius]
@[simp] theorem subst_oldLogQuery {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (oldLogQuery p z B a b) = oldLogQuery (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [oldLogQuery]
@[simp] theorem subst_squareData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (squareData z B a b) = squareData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [squareData]

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
    distanceBounded (ap2 f s x) (ap2 g t y) two (unit p) := by
  have S := GaussianExponentialReference.unit_monotone hs
  have T := GaussianExponentialReference.unit_monotone ht
  have budget : Γ ⊢[PRAAx] le ((unit s+unit t)*unit p) (two*(unit s*unit t)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit s) T) (mul_le_mul_right (unit t) S))
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t))
    (unit_positive p) budget (GaussianNameEquivalence.cross_at f g x y s t h)

theorem double_sample_error (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 doubleF p (doubleData z B a b)) (ap2 inputF p (leftData z R B a b))
      (two*amplification R) (unit p) := by
  let s := oldLogQuery p z B a b
  let t := GaussianBoundedConstantProductName.clock p (amplification R)
  let c := realMultiplier z B
  have sl : Γ ⊢[PRAAx] le p s := le_trans (le_add_right p (GaussianFastValueCut.normalizer two))
    (le_add_right _ _)
  have tl : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have dist := later_cross GaussianPositiveRationalLogarithm.logF GaussianHarmonicLogarithmName.nameF
    (GaussianPositiveRationalLogarithm.data a b) (GaussianHarmonicLogarithmName.data a b) p s t sl tl
    (GaussianHarmonicLogarithmName.cross_original a b h.andE₂.andE₁)
  have prod := GaussianNameArithmetic.product_distance c c _ _ zero two (unit p)
    (GaussianPositiveRationalLogarithm.radius a b) (amplification R) (unit_positive p)
    (GaussianRationalPowerDifference.distance_refl_zero c _ (unit_positive p)) dist
    (GaussianPositiveRationalLogarithm.sample_bound s a b h.andE₂.andE₁)
    (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁)
  exact distance_congr (double_sample p z B a b).eqSymm
    (GaussianBoundedConstantProductName.sample_at GaussianHarmonicLogarithmName.nameF p (amplification R) c
      (GaussianHarmonicLogarithmName.data a b)).eqSymm (by ipra_ring) (.eqRefl _) prod

theorem double_input_cross (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent doubleF inputF (doubleData z B a b) (leftData z R B a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (two*amplification R)
    (GaussianExponentialRealPart.double_real_regular _ _ (GaussianEulerIntegrandName.power_exponent_regular z B a b (old_source z R B a b h)))
    (GaussianEulerUpperPowerOrder.product_input _ _ _ _ h.andE₂ (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁)).andE₁
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,doubleF,doubleData,leftData,two] using
    double_sample_error (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) hs

theorem original_power_square (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent squareF expF (squareData z B a b) (leftExpData z R B a b) := by
  have old := GaussianEulerIntegrandName.power_input z B a b (old_source z R B a b h)
  have first := GaussianExponentialRealPart.exponential_norm_square powerExponentF (powerRadius z B a b) (powerExponentData z B a b) old
  have second := GaussianExponentialRadiusIndependence.independent_radii_proper doubleF inputF (doubleRadius z B a b) (radius R a)
    (doubleData z B a b) (leftData z R B a b) (GaussianExponentialRealPart.double_real_input _ _ _ old)
    (GaussianEulerUpperPowerOrder.product_input _ _ _ _ h.andE₂ (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₁))
    (double_input_cross z R B a b h)
  exact cross_trans _ _ _ _ _ _ first second

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
