import IPRADerivations.Analysis.GaussianGammaDigammaDerivativeProductOrder
import IPRADerivations.Analysis.GaussianEulerPositivePowerChartOrder

/-!
# Monotonicity of the native digamma name

The derivative product order allows cancellation of the two positive
Gamma factors. Their retimed observations have positive rational
decodings with a uniform lower bound, so the cancellation of each
diagonal rational comparison has a fixed finite observation budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaMonotone

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaDigammaNative (derivativeData derivative_regular gamma_times_digamma)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl cross_trans)
open GaussianNameRingLaws (multiply_sample_error multiply_associative multiply_commutative)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (qmul positive_product canonical_unique ofGaussian_canonical ofGaussian_represents)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qone qone_canonical)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGammaLogarithm (source gammaData gamma_regular gammaRetimedF gammaRetimedData gamma_retimed_cross
  gammaLogMargin log_input)
open RationalValueBounds (upper upper_mono upper_triangle upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "GF" => gammaRetimedF
local notation "gg" => gammaRetimedData

def weightF : PR 2 := multiplyF GF GF
def weightData (a c b : PTm n) : PTm n := multiplyData GF GF (gg a b) (gg c b)
def weightedF : PR 2 := multiplyF DF weightF
def leftData (a c b : PTm n) : PTm n := multiplyData DF weightF (dd a b) (weightData a c b)
def rightData (a c b : PTm n) : PTm n := multiplyData DF weightF (dd c b) (weightData a c b)

private theorem left_cross (a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) :
    Γ ⊢[PRAAx] crossEquivalent weightedF GaussianGammaDigammaDerivativeProductOrder.leftF
      (leftData a c b) (GaussianGammaDigammaDerivativeProductOrder.leftData a c b) := by
  let x := dd a b
  let y := gg a b
  let z := gg c b
  let v := gammaData a b
  let w := gammaData c b
  have hx := GaussianGammaDigammaNative.name_regular _ _ ha
  have hy := (log_input a b ha).andE₁
  have hz := (log_input c b hc).andE₁
  have hv := gamma_regular _ _ ha
  have hw := gamma_regular _ _ hc
  have root := multiply_cross DF DF GF gammaF x x y v hx hx hy hv (cross_refl _ _ hx)
    (cross_symm _ _ _ _ (gamma_retimed_cross a b ha))
  have term := cross_trans _ _ _ _ _ _ root (cross_trans _ _ _ _ _ _
    (multiply_commutative DF gammaF x v hx hv) (gamma_times_digamma a b ha))
  have replace := multiply_cross (multiplyF DF GF) IF GF gammaF (multiplyData DF GF x y) (derivativeData a b)
    z w (multiply_fast _ _ _ _ hx hy) (derivative_regular _ _ ha) hz hw term (cross_symm _ _ _ _ (gamma_retimed_cross c b hc))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative DF GF GF x y z hx hy hz)) replace

private theorem right_cross (a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) :
    Γ ⊢[PRAAx] crossEquivalent weightedF GaussianGammaDigammaDerivativeProductOrder.rightF
      (rightData a c b) (GaussianGammaDigammaDerivativeProductOrder.rightData a c b) := by
  let x := dd c b
  let y := gg a b
  let z := gg c b
  have hx := GaussianGammaDigammaNative.name_regular _ _ hc
  have hy := (log_input a b ha).andE₁
  have hz := (log_input c b hc).andE₁
  have swap := multiply_cross DF DF weightF weightF x x (weightData a c b) (weightData c a b) hx hx
    (multiply_fast _ _ _ _ hy hz) (multiply_fast _ _ _ _ hz hy) (cross_refl _ _ hx)
    (multiply_commutative GF GF y z hy hz)
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ (left_cross c a b hc ha)
    (multiply_commutative IF gammaF (derivativeData c b) (gammaData a b) (derivative_regular _ _ hc) (gamma_regular _ _ ha)))

def weightCost (a c b : PTm n) : PTm n := multiplyModulus GF GF (gg a b) (gg c b)+one
def sampleCost (x a c b : PTm n) : PTm n :=
  (multiplyModulus DF weightF x (weightData a c b)+one)+U DF x*weightCost a c b
def productCost (a c b : PTm n) : PTm n := sampleCost (dd a b) a c b+two+sampleCost (dd c b) a c b
def diagonalCost (a c b : PTm n) : PTm n := (gammaLogMargin*gammaLogMargin)*productCost a c b

private theorem sample_error (p x a c b : PTm n) (hx : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN DF x)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 weightedF p (multiplyData DF weightF x (weightData a c b)))
      (qmul (ap2 DF p x) (qmul (ap2 GF p (gg a b)) (ap2 GF p (gg c b)))) (sampleCost x a c b) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hy := (log_input a b ha).andE₁
  have hz := (log_input c b hc).andE₁
  have initial := multiply_sample_error DF weightF x (weightData a c b) p hx (multiply_fast _ _ _ _ hy hz)
  have last := multiply_sample_error GF GF (gg a b) (gg c b) p hy hz
  exact distance_triangle_same _ _ _ _ _ _ hp initial
    (GaussianNamedDifferenceQuotient.scale_distance (ap2 DF p x) _ _ (U DF x) _ (unit p) hp (sample_bound DF x p hx) last)

theorem raw_weighted_order (p a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    upper (fstT (qmul (ap2 DF p (dd a b)) (qmul (ap2 GF p (gg a b)) (ap2 GF p (gg c b)))))
      (fstT (qmul (ap2 DF p (dd c b)) (qmul (ap2 GF p (gg a b)) (ap2 GF p (gg c b)))))
      (productCost a c b) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have left := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp
    (sample_error p (dd a b) a c b (GaussianGammaDigammaNative.name_regular _ _ ha) ha hc))
  have right := scalar_upper _ _ _ _ hp (sample_error p (dd c b) a c b (GaussianGammaDigammaNative.name_regular _ _ hc) ha hc)
  have order := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (left_cross a c b ha hc)
    (cross_symm _ _ _ _ (right_cross a c b ha hc))
    (GaussianGammaDigammaDerivativeProductOrder.derivative_product_order a c b ha hc hac)
  have middle := upper_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp)
    (real_order_at weightedF weightedF (leftData a c b) (rightData a c b) p p order)
    (le_of_eq_add (d := zero) (by ipra_ring))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hp) hp)
    (upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left middle) right)
    (le_of_eq_add (d := zero) (by unfold productCost; ipra_ring))

private theorem fraction_inverse (d a : PTm n) (hd : Γ ⊢[PRAAx] le one d) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qmul (fraction d a) (fraction a d) ≐ qone := by
  have h := positive_product d a hd ha
  have same : Γ ⊢[PRAAx] fraction (d*a) (a*d) ≐ fraction (d*a) (d*a) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (mul_comm a d)
  exact (GaussianEulerDampedTimeRate.fraction_product d a a d ha hd).eqTrans
    (same.eqTrans (canonical_unique _ _ _ (d*a) (ofGaussian_canonical _ _ h) qone_canonical h
      (ofGaussian_represents _ _ h) (GaussianRationalReciprocal.qone_represents_scaled (d*a))))

set_option maxHeartbeats 800000 in
theorem diagonal_order (p a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    upper (fstT (ap2 DF p (dd a b))) (fstT (ap2 DF p (dd c b))) (diagonalCost a c b) (unit p) := by
  let u := GaussianNamedPositiveLogarithm.numerator GF p (gg a b)
  let v := GaussianNamedPositiveLogarithm.denominator GF p (gg a b)
  let x := GaussianNamedPositiveLogarithm.numerator GF p (gg c b)
  let y := GaussianNamedPositiveLogarithm.denominator GF p (gg c b)
  let A := u*x
  let D := v*y
  let M : PTm n := gammaLogMargin*gammaLogMargin
  let h := fraction A D
  let k := fraction D A
  let P := ap2 DF p (dd a b)
  let Q := ap2 DF p (dd c b)
  have hp := unit_positive (Γ := Γ) p
  have hL := GaussianNamedPositiveLogarithm.decoded_domain _ p _ _ _ (log_input a b ha)
  have hR := GaussianNamedPositiveLogarithm.decoded_domain _ p _ _ _ (log_input c b hc)
  have ha' : Γ ⊢[PRAAx] le one A := positive_product _ _ hL.andE₁.andE₁ hR.andE₁.andE₁
  have hd' : Γ ⊢[PRAAx] le one D := positive_product _ _ hL.andE₁.andE₂ hR.andE₁.andE₂
  have hu := GaussianNamedPositiveLogarithm.decoded_value _ p _ _ _ (log_input a b ha)
  have hx := GaussianNamedPositiveLogarithm.decoded_value _ p _ _ _ (log_input c b hc)
  have wt : Γ ⊢[PRAAx] qmul (ap2 GF p (gg a b)) (ap2 GF p (gg c b)) ≐ h :=
    (qmul_congr hu.eqSymm hx.eqSymm).eqTrans (GaussianEulerDampedTimeRate.fraction_product u v x y hL.andE₁.andE₂ hR.andE₁.andE₂)
  have scaled := GaussianEulerPositivePowerChartOrder.scale_upper D A (qmul P h) (qmul Q h) (productCost a c b) (unit p) ha'
    (upper_congr (congrFst (qmul_congr (.eqRefl _) wt)) (congrFst (qmul_congr (.eqRefl _) wt))
      (.eqRefl _) (.eqRefl _) (raw_weighted_order p a c b ha hc hac))
  have pos (z : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 DF p (dd z b)) :=
    GaussianNameArithmetic.multiply_canonical GaussianGammaC7Name.nameF IF
      (GaussianGammaDigammaNative.reciprocalData z b) (derivativeData z b) p
  have reduce (z : PTm n) : Γ ⊢[PRAAx] qmul k (qmul (ap2 DF p (dd z b)) h) ≐ ap2 DF p (dd z b) :=
    (qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative (ap2 DF p (dd z b)) h)).eqTrans
      (GaussianRationalInverseQuadraticAlgebra.cancel_nested_product k h _ (pos z) (fraction_inverse D A hd' ha'))
  have direct := upper_congr (congrFst (reduce a)) (congrFst (reduce c)) (.eqRefl _) (.eqRefl _) scaled
  have compare : Γ ⊢[PRAAx] le D (M*A) :=
    le_congr (.eqRefl _) (by dsimp only [M,A]; ipra_ring)
      (AnalyticNumberTheory.PhiLower.le_mul_mono hL.andE₂.andE₁ hR.andE₂.andE₁)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ ha' hp) direct
    (le_congr (by ipra_ring) (by unfold diagonalCost; dsimp only [M]; ipra_ring)
      (mul_le_mul_right (productCost a c b*unit p) compare))

theorem monotone_at (p q a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    upper (fstT (ap2 DF p (dd a b))) (fstT (ap2 DF q (dd c b))) (unit p+unit q) (unit p*unit q) := by
  let X := dd a b
  let Y := dd c b
  let K := diagonalCost a c b+two
  let t := GaussianNamedRealOrderTransport.precision (fstT (ap2 DF p X)) (fstT (ap2 DF q Y)) (unit p*unit q) K
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hl := GaussianGammaDigammaNative.name_regular _ _ ha
  have hr := GaussianGammaDigammaNative.name_regular _ _ hc
  have l := scalar_upper _ _ _ _ (positive_product _ _ hp ht) (GaussianNameEquivalence.point_at DF X p t hl)
  have r := scalar_upper _ _ _ _ (positive_product _ _ ht hq) (GaussianNameEquivalence.point_at DF Y t q hr)
  have join := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l (diagonal_order t a c b ha hc hac)) r
  apply GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ K
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hp ht) ht)
    (positive_product _ _ ht hq)) join
  exact le_of_eq_add (d := zero) (by unfold K; ipra_ring)

theorem monotone (a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx] realOrder DF DF (dd a b) (dd c b) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  refine .allI (.allI ?_)
  have aa : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift.shift
  have cc : Δ ⊢[PRAAx] source (sh c) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift.shift
  have ac : Δ ⊢[PRAAx] le (sh a) (sh c) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hac.shift.shift
  simpa only [realOrder,GaussianGammaDigammaNative.subst_data,Syn.shift,sh] using
    monotone_at (var 1) (var 0) _ _ _ aa cc ac

theorem actual_original_positive_rational_digamma_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 2) ⟶ source (var 1) (var 2) ⟶ le (var 0) (var 1) ⟶
      realOrder DF DF (dd (var 0) (var 2)) (dd (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (monotone _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaMonotone
