import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianRightHalfPlaneArgumentCosine
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneRadialLogarithm
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalSquareCancellation

/-!
# A margin for selecting the small-chart exponential

Multiply the nonnegative radial representative by the actual small-angle
exponential. Adding the encoded input gives a uniformly separated sum.
Its real numerator already gives the needed norm bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneExponentialMargin

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open GaussianCoefficientNameBounds (unit)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNamedBoundedProductObservation (clock name_at)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qadd qmul positive_product represents_rescale represents_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalLowerBounds (lower lower_congr)
open GaussianRationalNonnegativeFractions (fraction_at numerator denominator denominator_positive nonnegative_of_positive)
open GaussianPositiveRealArithmetic (sign)
open GaussianRightHalfPlaneArgument (smallF)
open GaussianRightHalfPlaneArgumentExponential (smallExpData)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen)
open RationalGaussianEmbedding (scalarZero)
open RationalSupMetric (denominatorOf)
open RationalValueBounds (upper)
open ComplexLogarithmRemainder (code re normSq scale oneCode mul add eval_re_code)
open GaussianRootAlgebra (equal_refl re_add re_mul re_scale re_one im_scale im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianRadiusExponentialName.nameF smallF
local notation "U" => GaussianPositiveRationalHalfLogarithm.positiveF
local notation "X" => GaussianPositiveRationalHalfLogarithm.positiveData

def point (A B D : PTm n) : PTm n := ofGaussian (code (ZT.ofNat A) (ZT.ofNat B)) D
def productF : PR 2 := multiplyF U V
def productData (A B D : PTm n) : PTm n := multiplyData U V (X (normNum A B) (normDen D)) (smallExpData A B)
def height (D : PTm n) : PTm n := exponent D zero

private theorem raw_real_natural (v : PTm n) (hv : Γ ⊢[PRAAx] sign (fstT v)) :
    ZT.toZ Γ (re (rawGaussian v)) =
      𝔞(GaussianPositiveRealArithmetic.numerator (fstT v)*denominatorOf (sndT v)) := by
  have e := natEq (eq_add_of_le hv)
  rw [rawGaussian,eval_re_code]
  rw [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [GaussianPositiveRealArithmetic.numerator,ZT.toZ,Q.mk_mul,map_mul]
  try simp only [Q.mk_add,map_add] at e
  linear_combination 𝔞(denominatorOf (sndT v))*e

theorem rational_sum_lower (u v A B D : PTm n) (hu : Γ ⊢[PRAAx] GaussianRationalHorner.canonical u)
    (hpos : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive u)
    (hv : Γ ⊢[PRAAx] upper scalarZero (fstT v) zero one)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] lower (qadd (qmul u v) (point A B D)) one D := by
  let a := numerator u
  let b := denominator u
  let e := rawDen v
  let z := code (ZT.ofNat A) (ZT.ofNat B)
  let c := mul (scale a oneCode) (rawGaussian v)
  let q := qmul u v
  let t := add (scale D c) (scale (b*e) z)
  let F := (b*e)*D
  let w := GaussianPositiveRealArithmetic.numerator (fstT v)*denominatorOf (sndT v)
  let J := qadd q (point A B D)
  have hb := denominator_positive (Γ := Γ) u
  have he := raw_den_positive (Γ := Γ) v
  have hbe := positive_product b e hb he
  have hF := positive_product _ _ hbe hD
  have uEq := fraction_at u hu (nonnegative_of_positive u hu hpos)
  have uRep : Γ ⊢[PRAAx] GaussianRationalHorner.represents u (scale a oneCode) b :=
    represents_congr uEq.eqSymm (equal_refl _) (.eqRefl _) (ofGaussian_represents _ _ hb)
  have prod := GaussianRationalHorner.qmul_represents u v _ _ b e hb he uRep (raw_represents v)
  have both := GaussianRationalHorner.qadd_represents q (point A B D) _ _ F hF
    (represents_rescale q c (b*e) D prod)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm D (b*e))
      (represents_rescale _ z D (b*e) (ofGaussian_represents z D hD)))
  have order : Γ ⊢[PRAAx] RationalArgmin.rationalLE scalarZero (fstT v) := by
    let p := RationalArgmin.left scalarZero (fstT v)
    let q := RationalArgmin.left (fstT v) scalarZero
    change Γ ⊢[PRAAx] le p q
    change Γ ⊢[PRAAx] le (one*p) (one*q+zero*denominatorOf scalarZero*denominatorOf (fstT v)) at hv
    exact le_congr (one_mul p) (by ipra_ring) hv
  have zeroSign : Γ ⊢[PRAAx] sign (scalarZero : PTm n) :=
    GaussianRationalL1.nonnegative_of_representation _ zero one (le_refl _)
      (RationalGaussianEmbedding.scalar_zero_represents one)
  have reV := raw_real_natural v (GaussianRationalL1.nonnegative_of_lower scalarZero (fstT v) zeroSign order)
  have er : ZT.toZ Γ (re t) = 𝔞(D*a*w+(b*e)*A) := by
    simp only [t,c,z,re_add,re_scale,re_mul,im_scale,re_one,im_one,eval_re_code,ZT.toZ_ofNat]
    rw [reV]
    unfold w
    ipra_simps
    ring
  let abs := zabs (re t)
  let δ := monus ((ZT.ofNat abs).pos+(re t).neg) ((re t).pos+(ZT.ofNat abs).neg)
  have absEq := zle_toZ (Γ := Γ) (GaussianRelativeNormTriangle.signed_le_absolute (re t))
  have hr : Γ ⊢[PRAAx] le (b*e) abs := by
    apply le_of_eq_add (d := D*a*w+(b*e)*monus A one+δ)
    apply deriveNat
    change ZT.toZ Γ (re t) + 𝔞 δ = ZT.toZ Γ (ZT.ofNat abs) at absEq
    rw [er,ZT.toZ_ofNat] at absEq
    have aa := natEq (eq_add_of_le hA)
    simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at aa absEq ⊢
    ipra_simps
    linear_combination -absEq + 𝔞 b*𝔞 e*aa
  have norm : Γ ⊢[PRAAx] le (abs*abs) (normSq t) :=
    le_congr (.eqRefl _) (GaussianCoordinateRadius.native_squared t).eqSymm (le_add_right _ _)
  exact GaussianRationalLowerBounds.lower_from_representation J t F one D hF hD both
    (le_congr (by dsimp [F] <;> ipra_ring) (.eqRefl _)
      (le_mul_mono (le_refl (D*D)) (le_trans (le_mul_mono hr hr) norm)))

theorem small_product_apart (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le B A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart (addF productF constantF)
      (height D) (addData (productData A B D) (point A B D)) := by
  let x := X (normNum A B) (normDen D)
  let y := smallExpData A B
  let q := point A B D
  let p := GaussianNameReciprocal.anchor (height D)
  let k := exponent two p
  let l := clock U V k x y
  let u := ap2 U l x
  let v := ap2 V l y
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical u := GaussianNameArithmetic.multiply_canonical _ _ _ _ _
  have hpos : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive u :=
    GaussianExponentialRealPart.square_sample_positive _ _ _
  have hv := GaussianRightHalfPlaneArgumentCosine.nonnegative_at l A B hA hB
  have base := rational_sum_lower u v A B D hc hpos hv hA hD
  have hzero : Γ ⊢[PRAAx] unit (zero : PTm n) ≐ one := pw_zero two
  have hb : Γ ⊢[PRAAx] le D (unit (height D)) :=
    le_congr ((congrMul (.eqRefl D) hzero).eqTrans (by ipra_ring)) (.eqRefl _) (query_budget D zero)
  have low := GaussianBoundedInverseApartness.weaken_denominator _ _ _ _ hD hb base
  have bind := (GaussianNameArithmetic.add_at (Γ := Γ) productF constantF (productData A B D) q p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qadd_congr
      (name_at U V k x y) (constant_at k q))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))
  exact lower_congr bind.eqSymm (.eqRefl _) (.eqRefl _) low

theorem actual_logarithm_small_chart_branch_apart_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ (le (var 1) (var 0) ⋏ le one (var 2))) ⟶
        GaussianNameReciprocal.apart (addF productF constantF) (height (var 2))
          (addData (productData (var 0) (var 1) (var 2)) (point (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (small_product_apart _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneExponentialMargin
