import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinIntegrand
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsParameterShift
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTransformedPower

/-!
# The Mellin integrand on the Euler lower-tail grid

On the chart for s-1, the original power in the Mellin integrand is
exactly the lower-tail Euler power multiplied by time. Time times the
actual Bose reciprocal is bounded by one. This preserves the original
Euler lower-tail majorant with an explicit observation allowance.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinOriginBound

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegrationByPartsParameterShift (powerProductF powerProductData original_power_parameter_shift)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerLowerPowerOrder (source)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaMellinIntegrand (reciprocalF reciprocalData reciprocal_bound)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiplyRaw)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Mellin" => GaussianGammaZetaMellinIntegrand.nameF
local notation "mellinData" => GaussianGammaZetaMellinIntegrand.data

private def comparisonF : PR 2 := multiplyF powerProductF reciprocalF
private def comparisonData (z D a b : PTm n) : PTm n :=
  multiplyData powerProductF reciprocalF (powerProductData z D a b) (reciprocalData a b)

private theorem comparison_agreement (z D a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z D a b) :
    Γ ⊢[PRAAx] crossEquivalent Mellin comparisonF
      (mellinData (shifted z D) D a b) (comparisonData z D a b) := by
  let r := reciprocalData a b
  have power := GaussianEulerIntegrandName.power_regular _ _ _ _ h
  have next := GaussianEulerIntegrandName.power_regular (shifted z D) D a b h
  have prod := GaussianNameArithmetic.multiply_fast _ _ _ _ (constant_regular (fraction a b)) power
  have inverse_regular := GaussianNameReciprocal.name_fast _ _ _
    (GaussianGammaZetaMellinIntegrand.denominator_regular a b)
    (GaussianGammaZetaMellinIntegrand.denominator_apart a b h.andE₂.andE₁ h.andE₂.andE₂)
  exact GaussianGammaAdjacentCutoff.multiply_cross powerF powerProductF reciprocalF reciprocalF
    (powerData (shifted z D) D a b) (powerProductData z D a b) r r next prod inverse_regular inverse_regular
    (original_power_parameter_shift z D a b h) (cross_refl _ _ inverse_regular)

private theorem time_times_reciprocal (p a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (qmul (fraction a b) (ap2 reciprocalF p (reciprocalData a b))) one one := by
  have t : Γ ⊢[PRAAx] bounded (fraction a b) a b :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded a b hb)
  have product := bounded_product _ _ a b b a hb ha t (reciprocal_bound p a b ha hb)
  exact bounded_radius_mono _ _ _ one one (positive_product _ _ hb ha) (le_refl one)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) product

private theorem comparison_bound (p z R D A a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R D A a b) :
    let a' := pw a A
    let b' := pw b A
    let W := pw b (pred A)
    let V := pw a (pred A)
    Γ ⊢[PRAAx] bounded (ap2 comparisonF p (comparisonData z D a' b'))
      (W*unit p+V) (V*unit p) := by
  let a' := pw a A
  let b' := pw b A
  let W := pw b (pred A)
  let V := pw a (pred A)
  let x := powerData z D a' b'
  let t := fraction a' b'
  let d := powerProductData z D a' b'
  let e := reciprocalData a' b'
  let m := GaussianFastValueCut.exponent (multiplyModulus powerProductF reciprocalF d e) p
  let k := GaussianFastValueCut.exponent (multiplyModulus constantF powerF t x) m
  let u := ap2 powerF k x
  let v := ap2 reciprocalF m e
  have source := GaussianEulerLowerTransformedPower.old_source z R D A a b h
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ h.andE₂.andE₁.andE₁
  have hk : Γ ⊢[PRAAx] le p k := le_trans (le_add_right _ _) (le_add_right _ _)
  have hu : Γ ⊢[PRAAx] bounded u (W*unit p+V) (V*unit p) := by
    have budget : Γ ⊢[PRAAx] le ((W*unit k+V)*(V*unit p)) ((W*unit p+V)*(V*unit k)) := by
      have growth := GaussianExponentialReference.unit_monotone hk
      ipra_le 𝔞(V*V)*sl growth
    exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hV (unit_positive k))
      (positive_product _ _ hV (unit_positive p)) budget
      (GaussianEulerLowerTransformedPower.original_power_bound k z R D A a b h)
  have weight : Γ ⊢[PRAAx] bounded (qmul t v) one one :=
    time_times_reciprocal m a' b' source.andE₂.andE₁ source.andE₂.andE₂
  have val : Γ ⊢[PRAAx] ap2 powerProductF m d ≐ qmul t u :=
    (GaussianNameArithmetic.multiply_at constantF powerF t x m).eqTrans
      ((GaussianNameArithmetic.recode_congr (qmul_congr (constant_at k t) (.eqRefl u))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))
  have read : Γ ⊢[PRAAx] ap2 comparisonF p (comparisonData z D a' b') ≐ qmul u (qmul t v) := by
    have outer := (GaussianNameArithmetic.multiply_at (Γ := Γ) powerProductF reciprocalF d e p).eqTrans
      (GaussianExponentialReference.recode_fixed (multiplyRaw powerProductF reciprocalF m d e) (qmul_canonical _ _))
    exact outer.eqTrans ((qmul_congr (val.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative t u))
      (.eqRefl v)).eqTrans (GaussianReciprocalHorner.qmul_associative u t v))
  exact bound_congr read.eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_product u (qmul t v) (W*unit p+V) (V*unit p) one one
      (positive_product _ _ hV (unit_positive p)) (le_refl one) hu weight)

theorem origin_bound (p z R D A a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R D A a b) :
    Γ ⊢[PRAAx] bounded (ap2 Mellin p (mellinData (shifted z D) D (pw a A) (pw b A)))
      (pw b (pred A)*unit p+num 3*pw a (pred A)) (pw a (pred A)*unit p) := by
  let a' := pw a A
  let b' := pw b A
  let W := pw b (pred A)
  let V := pw a (pred A)
  let U := unit p
  let x := mellinData (shifted z D) D a' b'
  let y := comparisonData z D a' b'
  let actual := ap2 Mellin p x
  let comp := ap2 comparisonF p y
  have hU := unit_positive (Γ := Γ) p
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ h.andE₂.andE₁.andE₁
  have hVU := positive_product _ _ hV hU
  have agreement := comparison_agreement z D a' b' (GaussianEulerLowerTransformedPower.old_source z R D A a b h)
  have dist := cross_at Mellin comparisonF x y p p agreement
  have diff : Γ ⊢[PRAAx] bounded (qsub actual comp) two U :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU hU) hU
      (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) dist
  have c : Γ ⊢[PRAAx] GaussianRationalHorner.canonical actual :=
    GaussianNameArithmetic.multiply_canonical powerF reciprocalF (powerData (shifted z D) D a' b')
      (reciprocalData a' b') p
  have sum := bounded_sum comp (qsub actual comp) (W*U+V) (V*U) two U hVU hU
    (comparison_bound p z R D A a b h) diff
  have summed := bound_congr (GaussianRationalLinearProduct.add_sub_right comp actual c) (.eqRefl _) (.eqRefl _) sum
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hVU hU) hVU ?_ summed
  change Γ ⊢[PRAAx] le (((W*U+V)*U+two*(V*U))*(V*U)) ((W*U+num 3*V)*(V*U*U))
  exact le_congr (.eqRefl _) (by ipra_ring) (le_refl _)

theorem actual_gamma_zeta_mellin_origin_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (ap2 Mellin (var 0) (mellinData (shifted (var 1) (var 3)) (var 3)
        (pw (var 5) (var 4)) (pw (var 6) (var 4))))
        (pw (var 6) (pred (var 4))*unit (var 0)+num 3*pw (var 5) (pred (var 4)))
        (pw (var 5) (pred (var 4))*unit (var 0))) :=
  closeUniv 7 (.impI (origin_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinOriginBound
