import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletPowerOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartTimeOrder
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianSquaredNormUpper

/-!
# A dyadic decay bound on actual Dirichlet rows

On the s-1 chart, for j at least (2^h)^A every requested sample of
the original j^(-s) has norm at most 1/(j*2^h)+3/2^p.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletRowDecay

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianEulerPositivePowerChart (argument)
open GaussianEulerUpperPowerCompatibility (squareF squareData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaEulerHeadShift (shifted)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qmul qmul_canonical)
open GaussianRationalMetric (bounded qnormSq qsub)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianEulerPositiveScalingConstant (inverseF inverseData)
open GaussianGammaZetaDirichletReciprocalRow (reciprocalRowF reciprocalRowData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def block (A h : PTm n) : PTm n := pw (unit h) A

ipra_subst block

theorem block_positive (A h : PTm n) : Γ ⊢[PRAAx] le one (block A h) :=
  GaussianPolynomialPerturbation.power_positive _ _ (unit_positive h)

private theorem exact_reference (A h : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] crossEquivalent powerF constantF
      (powerData (argument two A) A one (block A h)) (fraction one (unit h*unit h)) := by
  let U := unit h
  let J := block A h
  let ref := argument two A
  have src : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one U := .andI (le_refl one) (unit_positive h)
  have ej := AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) A
  have sd := GaussianEulerPowerInputProperness.original_power_proper ref A one J (pw one A) J hA
    (.andI (le_refl one) (block_positive A h)) (GaussianHarmonicLogarithmPower.power_source one U A src)
    ((mul_comm one J).eqTrans (congrMul (.eqRefl J) ej.eqSymm))
  have exact := GaussianEulerPowerChartRationalPowers.original_power two A one U hA src
  have twoStep : Γ ⊢[PRAAx] pw U two ≐ U*U :=
    (pw_succ U one).eqTrans (congrMul (pw_one U) (.eqRefl U))
  have endCode : Γ ⊢[PRAAx] fraction (pw one two) (pw U two) ≐ fraction one (U*U) := by
    simpa only [GaussianPositiveRationalLogarithm.subst_fraction,Syn.subst_var,Matrix.cons_val] using
      Prf.eqCongr (fraction (var 0) (var 1) : PTm 2) (σ := ![pw one two,pw U two]) (σ' := ![one,U*U])
        (fun i => by fin_cases i; exact AnalyticNumberTheory.Order.pw_one_base _; exact twoStep)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ sd
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ exact
      (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ endCode))

private theorem squared_order (z R B A h j : PTm n) (hs : Γ ⊢[PRAAx] S z R B A)
    (hj : Γ ⊢[PRAAx] le (block A h) j) : Γ ⊢[PRAAx] realOrder squareF constantF
      (squareData (shifted z B) B one j) (fraction one (unit h*unit h)) := by
  let ref := argument two A
  let J := block A h
  have hA := hs.andE₁.andE₁
  have jpos := le_trans (block_positive (Γ := Γ) A h) hj
  have ts : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one j := .andI (le_refl one) jpos
  have js : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one J :=
    .andI (le_refl one) (block_positive A h)
  have lower := GaussianGammaZetaDirichletPowerOrder.original_square_order z R B A one j hs ts jpos
  have margin : Γ ⊢[PRAAx] le two (two*A) :=
    le_congr (one_mul two) (mul_comm A two) (mul_le_mul_right two hA)
  have move := GaussianEulerPositivePowerChartOrder.original_power_order two A two one j one J hA margin ts js
    (le_congr (by ipra_ring) (by ipra_ring) hj)
  have result := GaussianEulerPowerChartTimeOrder.order_trans squareF powerF powerF
    (squareData (shifted z B) B one j) (powerData ref A one j) (powerData ref A one J) lower move
  have reg := GaussianEulerIntegrandName.power_regular (shifted z B) B one j
    (.andI hs.andE₁.andE₂.andE₁.andE₁ ts)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _
    _ (cross_refl _ _ (GaussianExponentialRealPart.square_regular _ _ reg)) (exact_reference A h hA) result

private theorem raw_power_bound (p z R B A h j : PTm n) (hs : Γ ⊢[PRAAx] S z R B A)
    (hj : Γ ⊢[PRAAx] le (block A h) j) :
    let x := powerData (shifted z B) B one j
    let t := GaussianExponentialRealPart.squarePrecision powerF (p+p) x
    Γ ⊢[PRAAx] bounded (ap2 powerF t x) (unit p+unit h) (unit h*unit p) := by
  let U := unit h
  let V := U*U
  let zz := shifted z B
  let x := powerData zz B one j
  let k := p+p
  let t := GaussianExponentialRealPart.squarePrecision powerF k x
  let a := qnormSq (ap2 powerF t x)
  let b := fstT (fraction one V)
  let q := GaussianNamedRealOrderTransport.precision a b (unit k) one
  have upper := real_order_at squareF constantF (squareData zz B one j) (fraction one V) k q
    (squared_order z R B A h j hs hj)
  have hUpper : Γ ⊢[PRAAx] RationalValueBounds.upper a b one (unit k) :=
    GaussianNamedRealOrderTransport.remove_upper_slack a b one (unit k) one
      (RationalValueBounds.upper_congr (GaussianEulerUpperPowerCompatibility.actual_squared_norm_sample k zz B one j)
        (congrFst (constant_at q (fraction one V))) (by ipra_ring) (.eqRefl _) upper)
  have rep := GaussianGammaHalfSqrtBrackets.fraction_first_represents (Γ := Γ) one V
    (positive_product U U (unit_positive h) (unit_positive h))
  exact GaussianSquaredNormUpper.bound_of_dyadic_squared_upper (ap2 powerF t x) b one U p (unit_positive h)
    (GaussianRationalHorner.scalar_congr (.eqRefl _) (by apply ZT.derive; ipra_simps; ring) (.eqRefl _) rep) hUpper |>
      bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)

theorem original_power_bound (p z R B A h j : PTm n) (hs : Γ ⊢[PRAAx] S z R B A)
    (hj : Γ ⊢[PRAAx] le (block A h) j) : Γ ⊢[PRAAx]
    bounded (ap2 powerF p (powerData (shifted z B) B one j)) (unit p+unit h) (unit h*unit p) := by
  let zz := shifted z B
  let x := powerData zz B one j
  let a := ap2 powerF p x
  let H := unit h
  let P := unit p
  let C := P+H
  let D := H*P
  let r := GaussianRationalSlackRemoval.precision a C D two
  let s := GaussianExponentialRealPart.squarePrecision powerF (r+r) x
  let b := ap2 powerF s x
  let V := unit r
  let W := unit s
  have hs' : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source zz B one j :=
    .andI hs.andE₁.andE₂.andE₁.andE₁ (.andI (le_refl one) (le_trans (block_positive A h) hj))
  have later : Γ ⊢[PRAAx] le r s := le_trans (le_add_right r r) (le_add_right _ _)
  have growth := GaussianExponentialReference.unit_monotone later
  have hP := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) r
  have hW := unit_positive (Γ := Γ) s
  have hH := unit_positive (Γ := Γ) h
  have diff := GaussianNameEquivalence.point_at powerF x p s (GaussianEulerIntegrandName.power_regular _ _ _ _ hs')
  have err := GaussianRationalDistanceOrder.distance_radius_mono a b _ _ (P+V) (P*V)
    (positive_product _ _ hP hW) (positive_product _ _ hP hV)
    (by change Γ ⊢[PRAAx] le ((P+W)*(P*V)) ((P+V)*(P*W)); ipra_le 𝔞(P*P)*sl growth) diff
  have norm := raw_power_bound r z R B A h j hs hj
  have total := bounded_sum b (qsub a b) (V+H) (H*V) (P+V) (P*V)
    (positive_product _ _ hH hV) (positive_product _ _ hP hV) norm err
  have read := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) b a
    (GaussianRadiusExponentialName.sample_canonical powerExponentF (powerRadius zz B one j) p (powerExponentData zz B one j))
  refine GaussianRationalSlackRemoval.slack_removal_at a C D two (positive_product _ _ hH hP) ?_
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hH hV) (positive_product _ _ hP hV))
    (positive_product _ _ (positive_product _ _ hH hP) hV) _
    (bound_congr read (.eqRefl _) (.eqRefl _) total)
  change Γ ⊢[PRAAx] le (((V+H)*(P*V)+(P+V)*(H*V))*(D*V))
    ((C*V+two*D)*(H*V*(P*V)))
  exact le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold C D; ipra_ring)

theorem row_decay (p z R B A h j : PTm n) (hs : Γ ⊢[PRAAx] S z R B A)
    (hj : Γ ⊢[PRAAx] le (block A h) j) : Γ ⊢[PRAAx]
    bounded (ap2 inverseF p (inverseData (shifted z B) B j one))
      (unit p+num 3*(j*unit h)) ((j*unit h)*unit p) := by
  let zz := shifted z B
  let x := powerData zz B one j
  let w := fraction one j
  let y := reciprocalRowData zz B j
  let I := ap2 inverseF p (inverseData zz B j one)
  let Y := ap2 reciprocalRowF p y
  let U := unit p
  let H := unit h
  let m := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF powerF w x) p
  let P := ap2 powerF m x
  have hB := hs.andE₁.andE₂.andE₁.andE₁
  have jpos := le_trans (block_positive (Γ := Γ) A h) hj
  have hU := unit_positive (Γ := Γ) p
  have hH := unit_positive (Γ := Γ) h
  have hJ := positive_product _ _ jpos hH
  have hD := positive_product _ _ hJ hU
  have hQ := positive_product _ _ hH (unit_positive (Γ := Γ) m)
  have growth : Γ ⊢[PRAAx] le U (unit m) := GaussianExponentialReference.unit_monotone (Γ := Γ)
    (le_add_right p (GaussianFastValueCut.normalizer (GaussianNameArithmetic.multiplyModulus constantF powerF w x)))
  have norm := bounded_radius_mono P _ _ (U+H) (H*U) hQ (positive_product _ _ hH hU)
    (by change Γ ⊢[PRAAx] le ((unit m+H)*(H*U)) ((U+H)*(H*unit m)); ipra_le 𝔞(H*H)*sl growth)
    (original_power_bound m z R B A h j hs hj)
  have weight : Γ ⊢[PRAAx] bounded w one j :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one j jpos).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one j jpos)
  have read : Γ ⊢[PRAAx] Y ≐ qmul w P :=
    (GaussianNameArithmetic.multiply_at constantF powerF w x p).eqTrans
      ((GaussianNameArithmetic.recode_congr (qmul_congr (constant_at m w) (.eqRefl P))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))
  have bound : Γ ⊢[PRAAx] bounded Y (U+H) ((j*H)*U) := bound_congr read.eqSymm (one_mul _) (by ipra_ring)
    (bounded_product w P one j (U+H) (H*U) jpos (positive_product _ _ hH hU) weight norm)
  have near : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded I Y (U+U) (U*U) :=
    cross_at inverseF reciprocalRowF (inverseData zz B j one) y p p
    (GaussianGammaZetaDirichletReciprocalRow.dirichlet_row_reciprocal zz B j hB jpos)
  have bd := bounded_radius_mono (qsub I Y) (U+U) (U*U) two U (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) near
  have sum := bounded_sum Y (qsub I Y) (U+H) ((j*H)*U) two U hD hU bound bd
  have value := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) Y I
    (GaussianRadiusExponentialName.sample_canonical
      (GaussianNameRingLaws.negativeF GaussianEulerPositiveScalingConstant.exponentF)
      (GaussianEulerPositiveScalingConstant.radius zz B j one) p
      (GaussianNameRingLaws.negativeData (GaussianEulerPositiveScalingConstant.exponentData zz B j one)))
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hU) hD _
    (bound_congr value (.eqRefl _) (.eqRefl _) sum)
  have grow : Γ ⊢[PRAAx] le H (j*H) :=
    le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H jpos)
  change Γ ⊢[PRAAx] le (((U+H)*U+two*((j*H)*U))*((j*H)*U))
    ((U+num 3*(j*H))*(((j*H)*U)*U))
  ipra_le 𝔞((j*H)*(U*U))*sl grow

theorem actual_original_Dirichlet_row_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (S (var 1) (var 2) (var 3) (var 4) ⟶ le (block (var 4) (var 5)) (var 6) ⟶
      bounded (ap2 inverseF (var 0) (inverseData (shifted (var 1) (var 3)) (var 3) (var 6) one))
        (unit (var 0)+num 3*(var 6*unit (var 5))) ((var 6*unit (var 5))*unit (var 0))) :=
  closeUniv 7 (.impI (.impI (row_decay _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletRowDecay
