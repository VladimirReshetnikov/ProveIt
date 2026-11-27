import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Convexity.GaussianGammaDigammaGammaComparison
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaDerivativeShift
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate

/-!
# Order of the original Gamma derivative products

The equal-step Gamma product order passes to the original first
logarithmic Euler integrals through the actual divided differences.
This yields Γ'(x)Γ(y) ≤ Γ(x)Γ'(y) for positive rationals x≤y.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDerivativeProductOrder

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaNative (derivativeData derivative_regular minimumDenominator)
open GaussianGammaDigammaStep (neighborData neighbor_source stepQuotientData step_rate)
open GaussianGammaDigammaGammaComparison (productF innerProductData outerProductData gamma_comparison)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameBounds (U sample_bound)
open GaussianNameRingLaws (multiply_sample_error through_identity)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedDifferenceQuotient (scale_distance inverse)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric distance_radius_mono)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGammaLogarithm (source gammaData gamma_regular)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "GF" => GaussianGammaDigammaGammaComparison.productF

def leftF : PR 2 := multiplyF IF gammaF
def rightF : PR 2 := multiplyF gammaF IF
def leftData (a c b : PTm n) : PTm n := multiplyData IF gammaF (derivativeData a b) (gammaData c b)
def rightData (a c b : PTm n) : PTm n := multiplyData gammaF IF (gammaData a b) (derivativeData c b)

ipra_subst leftData
ipra_subst rightData

theorem natural_inverse (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] inverse oneCode D ≐ naturalPoint D := by
  let w := GaussianRationalHorner.ofGaussian oneCode D
  let K := inverse oneCode D
  let r := naturalPoint D
  have e : Γ ⊢[PRAAx] qmul w r ≐ qone := by
    have h := GaussianEulerDampedTimeRate.fraction_product one D D one hD (le_refl one)
    have q : Γ ⊢[PRAAx] qmul w r ≐ fraction (one*D) (D*one) :=
      (qmul_congr (GaussianGammaDigammaStep.unit_step_value D hD).eqSymm (.eqRefl _)).eqTrans h
    have f : Γ ⊢[PRAAx] fraction (one*D) (D*one) ≐ fraction D D := GaussianCompactRiemannName.fraction_congr
      _ _ _ _ (by ipra_ring) (by ipra_ring)
    exact q.eqTrans (f.eqTrans (GaussianRationalHorner.canonical_unique _ _ _ D
      (GaussianRationalHorner.ofGaussian_canonical _ _ hD) qone_canonical hD
      (GaussianRationalHorner.ofGaussian_represents _ _ hD) (GaussianRationalReciprocal.qone_represents_scaled D)))
  have ax := GaussianNamedDifferenceQuotient.actual_inverse oneCode D
    (GaussianGammaUnitInverseSamples.actual_step_separated D hD)
  have ce := GaussianRationalInverseQuadraticAlgebra.cancel_nested_product K w r
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) ax
  exact (GaussianReciprocalHorner.qmul_one_right K (GaussianRationalReciprocal.reciprocal_canonical _)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) e.eqSymm).eqTrans ce)

def rawSlope (t a b D : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.raw gammaF gammaF t t (neighborData a b D) (gammaData a b) oneCode D
def quotientCost (a b D : PTm n) : PTm n := GaussianNamedDifferenceQuotient.cost gammaF gammaF
  (neighborData a b D) (gammaData a b) oneCode D
def gammaCost (a c b D : PTm n) : PTm n :=
  (multiplyModulus gammaF gammaF (neighborData a b D) (gammaData c b)+one)+two+
    (multiplyModulus gammaF gammaF (gammaData a b) (neighborData c b D)+one)

private theorem raw_gamma_order (t a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    upper (fstT (qmul (ap2 gammaF t (neighborData a b D)) (ap2 gammaF t (gammaData c b))))
      (fstT (qmul (ap2 gammaF t (gammaData a b)) (ap2 gammaF t (neighborData c b D)))) (gammaCost a c b D) (unit t) := by
  have hp := unit_positive (Γ := Γ) t
  have hL := multiply_sample_error gammaF gammaF (neighborData a b D) (gammaData c b) t
    (gamma_regular _ _ (neighbor_source a b D ha hD)) (gamma_regular _ _ hc)
  have hR := multiply_sample_error gammaF gammaF (gammaData a b) (neighborData c b D) t
    (gamma_regular _ _ ha) (gamma_regular _ _ (neighbor_source c b D hc hD))
  have left := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp hL)
  have right := scalar_upper _ _ _ _ hp hR
  have middle := upper_mono _ _ _ _ two (unit t) (positive_product _ _ hp hp)
    (real_order_at GF GF (innerProductData a c b D) (outerProductData a c b D) t t (gamma_comparison a c b D ha hc hac hD))
    (le_of_eq_add (d := zero) (by ipra_ring))
  have chain := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left middle) right
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hp) hp) chain
    (le_of_eq_add (d := zero) (by unfold gammaCost; ipra_ring))

theorem raw_slope_order (t a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    upper (fstT (qmul (rawSlope t a b D) (ap2 gammaF t (gammaData c b))))
      (fstT (qmul (ap2 gammaF t (gammaData a b)) (rawSlope t c b D))) (D*gammaCost a c b D) (unit t) := by
  let x := ap2 gammaF t (gammaData a b)
  let y := ap2 gammaF t (gammaData c b)
  let X := ap2 gammaF t (neighborData a b D)
  let Y := ap2 gammaF t (neighborData c b D)
  let v := qmul x y
  let z := qnegative v
  let k := inverse oneCode D
  have hp := unit_positive (Γ := Γ) t
  have triv := RationalValueBounds.upper_of_order (Γ := Γ) (fstT z) (fstT z) zero (unit t) (le_refl _)
  have diff := GaussianStirlingTailComparison.point_add_upper_same (qmul X y) (qmul x Y) z z
    (gammaCost a c b D) zero (unit t) hp (raw_gamma_order t a c b D ha hc hac hD) triv
  have eu : Γ ⊢[PRAAx] natScale D (qsub (qmul X y) v) ≐ qmul (rawSlope t a b D) y := by
    refine (natScale_as_product _ _).eqTrans ((qmul_congr (natural_inverse D hD).eqSymm ?_).eqTrans
      (qmul_associative k (qsub X x) y).eqSymm)
    exact (GaussianRationalSyntheticDivision.qsub_congr (qmul_commutative X y) (qmul_commutative x y)).eqTrans
      ((GaussianRationalRoundedPower.multiplication_difference y X x).eqTrans (qmul_commutative y (qsub X x)))
  have ev : Γ ⊢[PRAAx] natScale D (qsub (qmul x Y) v) ≐ qmul x (rawSlope t c b D) := by
    refine (natScale_as_product _ _).eqTrans ((qmul_congr (natural_inverse D hD).eqSymm
      (GaussianRationalRoundedPower.multiplication_difference x Y y)).eqTrans ?_)
    exact GaussianRationalPowerAlgebra.commute_nested k x (qsub Y y)
  exact upper_congr (congrFst eu) (congrFst ev) (by ipra_ring) (.eqRefl _)
    (GaussianRationalNaturalScaleOrder.scale_upper D _ _ _ _ diff)

theorem raw_slope_near (p t a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D)
    (ht : Γ ⊢[PRAAx] le (unit p) (unit t))
    (hCost : Γ ⊢[PRAAx] le (quotientCost a b D*unit p) (unit t)) : Γ ⊢[PRAAx]
      distanceBounded (rawSlope t a b D) (ap2 IF p (derivativeData a b)) (num 4) (unit p) := by
  let x := neighborData a b D
  let y := gammaData a b
  let q := stepQuotientData a b D
  have hp := unit_positive (Γ := Γ) p
  have ht' := unit_positive (Γ := Γ) t
  have sep := GaussianGammaDigammaStep.denominator_positive p a b D hD
  have hin := GaussianGammaDigammaDifferenceProduct.nativeInput a b D hs sep
  have read := GaussianNamedDifferenceQuotient.sample_error gammaF gammaF t x y oneCode D hin
  have h1 := distance_radius_mono _ _ _ _ one (unit p) ht' hp
    (le_congr (.eqRefl _) (one_mul _).eqSymm hCost) (distance_symmetric _ _ _ _ ht' read)
  have near := GaussianNamedInverseRate.rate_at QF IF q (derivativeData a b) one (unit p) t p (step_rate p a b D hs hD)
  have h2 := distance_radius_mono _ _ _ _ (num 3) (unit p)
    (GaussianNamedInverseRate.denominator_positive _ t p hp) hp (by
      unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
      ipra_le (𝔞 (unit p)*𝔞 (unit p))*sl ht) near
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp h1 h2)


def productCost (a c b : PTm n) : PTm n :=
  num 4*U gammaF (gammaData c b)+two*U IF (derivativeData a b)+
    (multiplyModulus IF gammaF (derivativeData a b) (gammaData c b)+one)

theorem product_near (p t a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D)
    (ht : Γ ⊢[PRAAx] le (unit p) (unit t)) (hCost : Γ ⊢[PRAAx] le (quotientCost a b D*unit p) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (qmul (rawSlope t a b D) (ap2 gammaF t (gammaData c b)))
      (ap2 leftF p (leftData a c b)) (productCost a c b) (unit p) := by
  let x := derivativeData a b
  let y := gammaData c b
  let g := ap2 gammaF t y
  let v := ap2 IF p x
  let r := rawSlope t a b D
  have hp := unit_positive (Γ := Γ) p
  have hx := derivative_regular _ _ ha
  have hy := gamma_regular _ _ hc
  have h1 := scale_distance g r v (U gammaF y) (num 4) (unit p) hp (sample_bound gammaF y t hy)
    (raw_slope_near p t a b D ha hD ht hCost)
  have d1 := distance_congr (qmul_commutative g r) (qmul_commutative g v)
    (by ipra_ring : Γ ⊢[PRAAx] U gammaF y*num 4 ≐ num 4*U gammaF y) (.eqRefl _) h1
  have gg := GaussianNameEquivalence.point_at gammaF y t p hy
  have gg' := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive t) hp) hp
    (by ipra_le 𝔞 (unit p)*sl ht) gg
  have h2 := scale_distance v g (ap2 gammaF p y) (U IF x) two (unit p) hp (sample_bound IF x p hx) gg'
  have d2 := distance_congr (.eqRefl _) (.eqRefl _)
    (by ipra_ring : Γ ⊢[PRAAx] U IF x*two ≐ two*U IF x) (.eqRefl _) h2
  have h3 := distance_symmetric _ _ _ _ hp (multiply_sample_error IF gammaF x y p hx hy)
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp d1 d2) h3

def diagonalCost (a c b : PTm n) : PTm n := productCost a c b+one+(productCost c a b+two)

set_option maxHeartbeats 800000 in
theorem diagonal_order (p a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] upper (fstT (ap2 leftF p (leftData a c b))) (fstT (ap2 rightF p (rightData a c b)))
      (diagonalCost a c b) (unit p) := by
  let D := minimumDenominator p a b+minimumDenominator p c b
  let K := ((one+quotientCost a b D)+quotientCost c b D)+D*gammaCost a c b D
  let t := GaussianFastValueCut.exponent K p
  have hp := unit_positive (Γ := Γ) p
  have ht' := unit_positive (Γ := Γ) t
  have hda : Γ ⊢[PRAAx] le (minimumDenominator p a b) D := le_add_right _ _
  have hdc : Γ ⊢[PRAAx] le (minimumDenominator p c b) D := le_add_left _ _
  have hd := GaussianGammaDigammaStep.denominator_positive p a b D hda
  have late (N : PTm n) (h : Γ ⊢[PRAAx] le N K) : Γ ⊢[PRAAx] le (N*unit p) (unit t) :=
    le_trans (mul_le_mul_right _ h) (GaussianFastValueCut.query_budget _ _)
  have ht := le_congr (one_mul _ ) (.eqRefl _) (late one (le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)))
  have hm := late (D*gammaCost a c b D) (le_add_left _ _)
  have hl := late (quotientCost a b D) (le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) (le_add_right _ _))
  have hr := late (quotientCost c b D) (le_trans (le_add_left _ _) (le_add_right _ _))
  have s := raw_slope_order t a c b D ha hc hac hd
  have mid := upper_mono _ _ _ _ one (unit p) ht' s (le_congr (.eqRefl _) (one_mul _).eqSymm hm)
  have l := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (product_near p t a c b D ha hc hda ht hl))
  have raw := product_near p t c a b D hc ha hdc ht hr
  have r := scalar_upper _ _ _ _ hp
    (distance_congr (qmul_commutative _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)
  have swap := GaussianNameRingLaws.multiply_commutative IF gammaF (derivativeData c b) (gammaData a b)
    (derivative_regular _ _ hc) (gamma_regular _ _ ha)
  have hswap := upper_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp)
    (scalar_upper _ _ _ _ (positive_product _ _ hp hp) (GaussianNameEquivalence.cross_at _ _ _ _ p p swap))
    (le_of_eq_add (d := zero) (by ipra_ring))
  have tail := upper_triangle _ _ _ _ _ _ _ r hswap
  have res := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l mid) tail
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hp) (positive_product _ _ hp hp)) res
    (le_of_eq_add (d := zero) (by unfold diagonalCost; ipra_ring))

theorem product_order_at (p q a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] upper (fstT (ap2 leftF p (leftData a c b))) (fstT (ap2 rightF q (rightData a c b)))
      (unit p+unit q) (unit p*unit q) := by
  let X := leftData a c b
  let Y := rightData a c b
  let K := diagonalCost a c b+two
  let t := GaussianNamedRealOrderTransport.precision (fstT (ap2 leftF p X)) (fstT (ap2 rightF q Y)) (unit p*unit q) K
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hl := multiply_fast IF gammaF (derivativeData a b) (gammaData c b) (derivative_regular _ _ ha) (gamma_regular _ _ hc)
  have hr := multiply_fast gammaF IF (gammaData a b) (derivativeData c b) (gamma_regular _ _ ha) (derivative_regular _ _ hc)
  have l := scalar_upper _ _ _ _ (positive_product _ _ hp ht) (GaussianNameEquivalence.point_at leftF X p t hl)
  have r := scalar_upper _ _ _ _ (positive_product _ _ ht hq) (GaussianNameEquivalence.point_at rightF Y t q hr)
  have join := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l (diagonal_order t a c b ha hc hac)) r
  apply GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ K
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hp ht) ht)
    (positive_product _ _ ht hq)) join
  exact le_of_eq_add (d := zero) (by unfold K; ipra_ring)

theorem derivative_product_order (a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] realOrder leftF rightF (leftData a c b) (rightData a c b) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  refine .allI (.allI ?_)
  have aa : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift.shift
  have cc : Δ ⊢[PRAAx] source (sh c) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift.shift
  have ac : Δ ⊢[PRAAx] le (sh a) (sh c) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hac.shift.shift
  simpa only [realOrder,subst_leftData,subst_rightData,Syn.shift,sh] using product_order_at (var 1) (var 0) _ _ _ aa cc ac

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDerivativeProductOrder
