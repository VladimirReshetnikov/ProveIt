import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveLinearStep
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFirstOrderProductError

/-!
# A compact cell estimate for the actual beta quadrature row

Both primitive endpoints use the observation clock belonging to the
original evaluator at that endpoint. The polynomial factor is exact.
The local residual has a quadratic physical-time step term, uniformly
on the positive compact interval for the fixed original degree, and
an explicit dyadic observation term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveCompactStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaPrimitiveLinearStep (argument step sample linearSum)
open GaussianBetaKernelGridComparison (row)
open GaussianEulerCompactProductComparison (clock clock_later)
open GaussianEulerPowerIncrement (point slopeTerm)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianTimeWeightedPolynomialIncrement (value linear residual quadraticBound)
open GaussianRationalUniformFirstOrderPolynomial (mass slopeConstant)
open GaussianRationalHorner (qmul qadd positive_product ofGaussian_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def polynomialBound (z B N : PTm n) : PTm n := mass (primitive z B N) one
def polynomialRemainder (z B N : PTm n) : PTm n := quadraticBound (primitive z B N) N one
def polynomialVariation (z B N : PTm n) : PTm n :=
  polynomialRemainder z B N+(slopeConstant (primitive z B N) N one+polynomialBound z B N)
def powerRemainder (R E T : PTm n) : PTm n :=
  (E*E)*(GaussianRadiusExponentialLipschitzRate.factor (GaussianEulerPowerShiftRate.radius R E T)*(R+one)
    +majorant R E T*((R+one)*(R+one)))
def powerLinear (R E T : PTm n) : PTm n := majorant R E T*(R+one)*E
def curvature (z R B E T N : PTm n) : PTm n :=
  powerRemainder R E T*polynomialBound z B N+majorant R E T*polynomialRemainder z B N+
    powerLinear R E T*polynomialVariation z B N

def numerator (p z R B E T b c N : PTm n) : PTm n :=
  curvature z R B E T N*c*c*unit p+num 6*polynomialBound z B N*(b*b)
def denominator (p b : PTm n) : PTm n := (b*b)*unit p
def endpoint (p z B a b N : PTm n) : PTm n := sample (clock p z B a b) z B a b N
def cell (p z B a b c N : PTm n) : PTm n := qmul (row p z B a b N) (step c b N)

def source (z R B A E T a b c N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
  (GaussianEulerPowerShiftRate.source z R B E T a b c ⋏ (le one N ⋏ le (a+c) (b*N)))

private theorem fraction_bound (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (fraction a b) a b :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded a b hb)

private theorem argument_bound (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] le a (b*N)) :
    Γ ⊢[PRAAx] bounded (argument a b N) one one := by
  have d := positive_product b N hb hN
  have cmp : Γ ⊢[PRAAx] le (a*one) (one*(b*N)) := le_congr (by ipra_ring) (by ipra_ring) h
  exact bounded_radius_mono _ _ _ _ _ d (le_refl _) cmp (fraction_bound a (b*N) d)

private theorem polynomial_value (z B N t : PTm n) (ht : Γ ⊢[PRAAx] bounded t one one) :
    Γ ⊢[PRAAx] bounded (value (primitive z B N) t) (polynomialBound z B N) one :=
  bound_congr (.eqRefl _) (by unfold polynomialBound; ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _)
      (GaussianRationalUniformFirstOrderPolynomial.value_bound _ _ one (le_refl _) ht) ht)

private theorem polynomial_errors (z B a b c N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) (hEnd : Γ ⊢[PRAAx] le (a+c) (b*N)) :
    let C := primitive z B N
    let u := argument a b N
    let v := argument (a+c) b N
    let h := step c b N
    let diff := qsub (value C v) (value C u)
    (Γ ⊢[PRAAx] bounded (qsub diff (qmul h (linear C u N))) (polynomialRemainder z B N*c*c) (b*b)) ∧
    (Γ ⊢[PRAAx] bounded diff (polynomialVariation z B N*c) b) := by
  dsimp only
  let C := primitive z B N
  let D := b*N
  let u := argument a b N
  let v := argument (a+c) b N
  let h := step c b N
  let W := polynomialRemainder z B N
  let L := slopeConstant C N one+polynomialBound z B N
  let weightedLinear := qmul h (linear C u N)
  let delta := qsub (value C v) (value C u)
  have hD : Γ ⊢[PRAAx] le one D := positive_product b N hb hN
  have hD2 := positive_product _ _ hD hD
  have hb2 := positive_product b b hb hb
  have hD_ge : Γ ⊢[PRAAx] le b D := by
    have order : Γ ⊢[PRAAx] le (one*b) (N*b) := mul_le_mul_right b hN
    exact le_congr (one_mul b) (by dsimp only [D]; ipra_ring) order
  have hc_le : Γ ⊢[PRAAx] le c D :=
    le_trans (le_of_eq_add (d := a) (by ipra_ring)) hEnd
  have hu : Γ ⊢[PRAAx] bounded u one one :=
    argument_bound a b N hb hN (le_trans (le_add_right a c) hEnd)
  have hv : Γ ⊢[PRAAx] bounded v one one := argument_bound (a+c) b N hb hN hEnd
  have hstep : Γ ⊢[PRAAx] bounded h c D := fraction_bound c D hD
  have sh : Γ ⊢[PRAAx] qadd u h ≐ v := GaussianBetaPrimitiveLinearStep.argument_step a b c N hb hN
  have valEq : Γ ⊢[PRAAx] value C (qadd u h) ≐ value C v :=
    qmul_congr (GaussianRationalTranslation.evaluate_congr (.eqRefl _) sh) sh
  have shifted : Γ ⊢[PRAAx] bounded (qadd u h) one one :=
    bound_congr sh.eqSymm (.eqRefl _) (.eqRefl _) hv
  have rem :=
    GaussianTimeWeightedPolynomialIncrement.original_weighted_remainder C u h N one c D
      (GaussianEulerBetaPolynomialPrimitive.primitive_length z B N) (le_refl _) hu shifted hD hstep
      (ofGaussian_canonical _ _ hD)
  have atStep : Γ ⊢[PRAAx] bounded (qsub delta weightedLinear) (W*c*c) (D*D) :=
    bound_congr (qsub_congr (qsub_congr valEq (.eqRefl _)) (.eqRefl _)) (.eqRefl _) (.eqRefl _) rem
  have small : Γ ⊢[PRAAx] bounded (qsub delta weightedLinear) (W*c*c) (b*b) := by
    apply bounded_radius_mono _ _ _ _ _ hD2 hb2 ?_ atStep
    have ord := AnalyticNumberTheory.PhiLower.le_mul_mono hD_ge hD_ge
    ipra_le (𝔞 W*𝔞 c*𝔞 c)*sl ord
  have slopeRaw := bounded_product (GaussianRationalFirstOrderPolynomial.slope C u N) u
    (slopeConstant C N one) one one one (le_refl _) (le_refl _)
    (GaussianRationalUniformFirstOrderPolynomial.slope_bound C u N one
      (GaussianEulerBetaPolynomialPrimitive.primitive_length z B N) (le_refl _) hu) hu
  have slopeBound : Γ ⊢[PRAAx] bounded (qmul (GaussianRationalFirstOrderPolynomial.slope C u N) u)
      (slopeConstant C N one) one := bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) slopeRaw
  have sumBound : Γ ⊢[PRAAx] bounded (linear C u N) L one :=
    bounded_sum_same _ _ _ _ _ (le_refl _) slopeBound
      (GaussianRationalUniformFirstOrderPolynomial.value_bound C u one (le_refl _) hu)
  have linearBound : Γ ⊢[PRAAx] bounded weightedLinear (L*c) D :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ hD (le_refl _) hstep sumBound)
  have remLinear : Γ ⊢[PRAAx] bounded (qsub delta weightedLinear) (W*c) D := by
    apply bounded_radius_mono _ _ _ _ _ hD2 hD ?_ atStep
    ipra_le (𝔞 W*𝔞 c*𝔞 D)*sl hc_le
  have sum := bounded_sum_same weightedLinear (qsub delta weightedLinear) _ _ _ hD linearBound remLinear
  have varBound : Γ ⊢[PRAAx] bounded delta ((W+L)*c) D :=
    bound_congr (GaussianRationalLinearProduct.add_sub_right weightedLinear delta (qsub_canonical _ _))
      (by ipra_ring) (.eqRefl _) sum
  refine ⟨small, bounded_radius_mono _ _ _ _ _ hD hb ?_ varBound⟩
  change Γ ⊢[PRAAx] le (((W+L)*c)*b) (((W+L)*c)*D)
  ipra_le ((𝔞 W+𝔞 L)*𝔞 c)*sl hD_ge

/-- A single original beta row is the first-order increment of the
sampled primitive on a positive compact subinterval of the support. -/
theorem original_cell_error (p z R B A E T a b c N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A E T a b c N) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (endpoint p z B (a+c) b N) (endpoint p z B a b N))
      (cell p z B a b c N) (numerator p z R B E T b c N) (denominator p b) := by
  let s := clock p z B (a+c) b
  let t := clock p z B a b
  let P := unit s
  let Q := unit t
  let U := unit p
  let b2 := b*b
  let V := b2*(P*Q)
  let D := denominator p b
  let q1 := point s z B (a+c) b
  let q0 := point t z B a b
  let C := primitive z B N
  let y1 := value C (argument (a+c) b N)
  let y0 := value C (argument a b N)
  let L := slopeTerm t z B a b c
  let M := qmul (step c b N) (linear C (argument a b N) N)
  let X := majorant R E T
  let Z := polynomialBound z B N
  let W := polynomialRemainder z B N
  let Y := polynomialVariation z B N
  let K := powerRemainder R E T
  let J := powerLinear R E T
  let ex := GaussianRationalFirstOrderProductError.error q1 q0 L
  let ey := GaussianRationalFirstOrderProductError.error y1 y0 M
  let raw := K*c*c*(P*Q)+(Q+num 5*P)*b2
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have ht := unit_positive (Γ := Γ) t
  have huP : Γ ⊢[PRAAx] le U P := GaussianExponentialReference.unit_monotone (clock_later p z B (a+c) b)
  have huQ : Γ ⊢[PRAAx] le U Q := GaussianExponentialReference.unit_monotone (clock_later p z B a b)
  have sh := h.andE₂.andE₁
  have ha := sh.andE₂.andE₁.andE₁.andE₁
  have hb := sh.andE₂.andE₁.andE₁.andE₂
  have hN := h.andE₂.andE₂.andE₁
  have endTime := h.andE₂.andE₂.andE₂
  have hb2 : Γ ⊢[PRAAx] le one b2 := positive_product _ _ hb hb
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ hb2 (positive_product _ _ hs ht)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hb2 hp
  have power := GaussianEulerPowerIncrement.compact_power_increment s t z R B E T a b c sh
  have bex : Γ ⊢[PRAAx] bounded ex raw V := by
    apply bound_congr (.eqRefl _) ?_ (.eqRefl _) power
    dsimp only [GaussianEulerPowerIncrement.compactNumerator,GaussianEulerPowerIncrement.curvature,
      GaussianEulerPowerIncrement.productRemainder,GaussianEulerPowerExponentialShift.coefficient,
      GaussianEulerPowerShiftRate.numerator,raw,K,powerRemainder,P,Q,b2]
    ipra_ring
  have bounds := polynomial_errors z B a b c N hb hN endTime
  have by1 : Γ ⊢[PRAAx] bounded y1 Z one := polynomial_value _ _ _ _ (argument_bound _ _ _ hb hN endTime)
  have bq0 : Γ ⊢[PRAAx] bounded q0 X one :=
    original_power_observation t z R B E T a b sh.andE₁ sh.andE₂.andE₁
  have bL : Γ ⊢[PRAAx] bounded L (J*c) b := by
    have line := GaussianEulerPowerExponentIncrement.linear_bound z R B a c
      sh.andE₁.andE₁ sh.andE₁.andE₂.andE₂ ha
    have prod := bounded_product q0 _ X one ((R+one)*c) a (le_refl _) ha bq0 line
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl _) ha) hb ?_ prod
    have left := sh.andE₂.andE₁.andE₂.andE₁
    dsimp only [J,powerLinear]
    ipra_le (𝔞 X*(𝔞 R+1)*𝔞 c)*sl left
  have first : Γ ⊢[PRAAx] bounded (qmul ex y1) (raw*Z) V :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ hv (le_refl _) bex by1)
  have second : Γ ⊢[PRAAx] bounded (qmul q0 ey) (X*W*c*c) b2 :=
    bound_congr (.eqRefl _) (by ipra_ring) (one_mul _)
      (bounded_product _ _ _ _ _ _ (le_refl _) hb2 bq0 bounds.1)
  have third : Γ ⊢[PRAAx] bounded (qmul L (qsub y1 y0)) (J*Y*c*c) b2 :=
    bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (bounded_product _ _ _ _ _ _ hb hb bL bounds.2)
  have prodBound := bounded_sum_same _ _ _ _ _ hb2 second third
  have assoc := GaussianRationalSumAlgebra.qadd_associative (Γ := Γ) (qmul ex y1) (qmul q0 ey) (qmul L (qsub y1 y0))
  have scaled : Γ ⊢[PRAAx] bounded (qadd (qmul q0 ey) (qmul L (qsub y1 y0)))
      ((X*W*c*c+J*Y*c*c)*(P*Q)) V :=
    bounded_radius_mono _ _ _ _ _ hb2 hv (le_of_eq_add (d := zero) (by dsimp only [V]; ipra_ring)) prodBound
  have sum := bounded_sum_same _ _ _ _ _ hv first scaled
  have norm : Γ ⊢[PRAAx] bounded (GaussianRationalFirstOrderProductError.productError q1 q0 y1 y0 L M)
      (raw*Z+(X*W*c*c+J*Y*c*c)*(P*Q)) V :=
    bound_congr (((GaussianRationalFirstOrderProductError.product_error_identity q1 q0 y1 y0 L M).eqTrans assoc).eqSymm)
      (.eqRefl _) (.eqRefl _) sum
  have uniform : Γ ⊢[PRAAx] bounded (GaussianRationalFirstOrderProductError.productError q1 q0 y1 y0 L M)
      (numerator p z R B E T b c N) D := by
    apply bounded_radius_mono _ _ _ _ _ hv hD ?_ norm
    change Γ ⊢[PRAAx] le
      ((raw*Z+(X*W*c*c+J*Y*c*c)*(P*Q))*(b2*U))
      ((curvature z R B E T N*c*c*U+num 6*Z*b2)*(b2*(P*Q)))
    dsimp only [raw,curvature,K,Z,X,W,J,Y,b2]
    ipra_le ((𝔞 b*𝔞 b)*(𝔞 b*𝔞 b)*𝔞 (polynomialBound z B N)*𝔞 Q)*sl huP+
      (5*(𝔞 b*𝔞 b)*(𝔞 b*𝔞 b)*𝔞 (polynomialBound z B N)*𝔞 P)*sl huQ
  exact bound_congr (qsub_congr (.eqRefl _)
    (GaussianBetaPrimitiveLinearStep.actual_row_linear_sum p z R B A a b c N h.andE₁ ha hb hN))
    (.eqRefl _) (.eqRefl _) uniform

theorem original_beta_primitive_compact_cell_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded (qsub (endpoint (var 0) (var 1) (var 3) (var 7+var 9) (var 8) (var 10))
        (endpoint (var 0) (var 1) (var 3) (var 7) (var 8) (var 10)))
        (cell (var 0) (var 1) (var 3) (var 7) (var 8) (var 9) (var 10))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 8) (var 9) (var 10))
        (denominator (var 0) (var 8))) :=
  closeUniv 11 (.impI (original_cell_error _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveCompactStep
