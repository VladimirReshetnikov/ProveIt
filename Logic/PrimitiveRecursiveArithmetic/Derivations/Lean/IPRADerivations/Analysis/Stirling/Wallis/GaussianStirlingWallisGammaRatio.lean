import IPRADerivations.Analysis.Stirling.Wallis.GaussianStirlingWallisFactor
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfIntegerValues
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSquareLimit
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Identities.GaussianNamedProductSquare

/-!
# Original Gamma names in the Stirling half-step Wallis ratio

At (n=r+1), the actual squared half-integer Gamma divided by the
literal positive divisor (n(r!)^2) equals the original π name
multiplied by the checked rational Wallis coefficient. The actual
integer Gamma supplies exactly the same divisor.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingWallisGammaRatio

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_source gamma_source_at_radius gamma_regular)
open GaussianStirlingWallisFactor (halfSquareFactor integerDivisor inverseIntegerDivisor ratioFactor
  half_square_code factor_from_products)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianNamedProductSquare (square_product)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRootAlgebra (equal equal_of_values equal_symm)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF
local notation "G" => gammaF
local notation "V" => GaussianGammaHalfIntegerValues.valueF

def halfNumerator (r : PTm n) : PTm n := two*succ r+one
def halfData (r : PTm n) : PTm n := gammaData (halfNumerator r) two
def integerData (r : PTm n) : PTm n := gammaData (succ r) one
def halfSquareF : PR 2 := multiplyF G G
def halfSquareData (r : PTm n) : PTm n := multiplyData G G (halfData r) (halfData r)
def ratioF : PR 2 := multiplyF halfSquareF C
def ratioData (r : PTm n) : PTm n := multiplyData halfSquareF C (halfSquareData r) (inverseIntegerDivisor r)
def wallisF : PR 2 := multiplyF P C
def wallisData (r x : PTm n) : PTm n := multiplyData P C x (ratioFactor (succ r))

ipra_subst halfNumerator [two, one]
ipra_subst halfData [two, one]
ipra_subst integerData [one]
ipra_subst halfSquareData
ipra_subst ratioData
ipra_subst wallisData

theorem half_source (r : PTm n) : Γ ⊢[PRAAx] source (halfNumerator r) two :=
  .andI (by unfold halfNumerator; ipra_le 2*𝔞 (succ r)) (le_succ_self one)

theorem half_regular (r : PTm n) : Γ ⊢[PRAAx] pointCN G (halfData r) :=
  gamma_regular _ _ (half_source r)

private theorem argument_value (N B target : PTm n) (h : Γ ⊢[PRAAx] target ≐ one+B*N) :
    Γ ⊢[PRAAx] equal (arg target) (GaussianGammaShiftTrajectory.point oneCode B N) := by
  let w := GaussianGammaShiftTrajectory.point oneCode B N
  have native := GaussianGammaShiftTrajectory.point_native (Γ := Γ) oneCode B N
  have e := natEq h
  apply equal_of_values
  · change ZT.toZ Γ (ComplexLogarithmRemainder.re (arg target)) = ZT.toZ Γ (ComplexLogarithmRemainder.re w)
    rw [GaussianRootAlgebra.equal_re native]
    simp only [arg,GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination e
  · change ZT.toZ Γ (ComplexLogarithmRemainder.im (arg target)) = ZT.toZ Γ (ComplexLogarithmRemainder.im w)
    rw [GaussianRootAlgebra.equal_im native]
    simp only [arg,GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.im_one]
    ring

theorem half_input_cross (r : PTm n) : Γ ⊢[PRAAx] crossEquivalent G G (halfData r)
    (GaussianGammaHalfIntegerValues.gammaInput (succ r)) := by
  let N := succ r
  let a := halfNumerator r
  let u := arg a
  let v := GaussianGammaHalfIntegerDomain.argument N
  let R := GaussianGammaHalfIntegerDomain.radius N
  have h := half_source (Γ := Γ) r
  have hr : Γ ⊢[PRAAx] le one R := le_add_right one N
  have disk : Γ ⊢[PRAAx] le a (R*two) := by
    dsimp only [R,a,GaussianGammaHalfIntegerDomain.radius,halfNumerator,N]
    ipra_le 1
  have input := gamma_source_at_radius a two R h hr disk
  have align : Γ ⊢[PRAAx] equal u v :=
    argument_value N two a (by unfold a halfNumerator N; ipra_ring)
  have radii := GaussianGammaRadiusOverlap.original_Gamma_overlap u a R two one two one two (gamma_source a two h) input
  exact cross_trans _ _ _ _ _ _ radii (GaussianGammaInputProperness.original_Gamma_proper u v R two one two input align)

theorem half_factorial_cross (r : PTm n) : Γ ⊢[PRAAx] crossEquivalent G V (halfData r)
    (GaussianGammaHalfIntegerValues.valueData (succ r)) :=
  cross_trans _ _ _ _ _ _ (half_input_cross r) (GaussianGammaHalfIntegerValues.original_half_integer_value (succ r))

theorem integer_factorial_cross (r : PTm n) : Γ ⊢[PRAAx] crossEquivalent G C (integerData r)
    (GaussianGammaFactorialValues.factorialValue r) := by
  let N := succ r
  let a := arg N
  let b := GaussianGammaFactorialValues.argument r
  have h : Γ ⊢[PRAAx] source N one := .andI (zero_lt_succ r) (le_refl one)
  have e : Γ ⊢[PRAAx] equal a b := argument_value r one N (by unfold N; ipra_ring)
  have moved := GaussianGammaInputProperness.original_Gamma_proper a b N one one one (gamma_source N one h) e
  have align : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.gammaData b N one one ≐ GaussianGammaFactorialValues.data r :=
    GaussianGammaFactorialValues.gamma_fields_congr (.eqRefl _) (by unfold N GaussianGammaFactorialValues.radius; ipra_ring)
      (.eqRefl _) (.eqRefl _)
  exact cross_trans _ _ _ _ _ _ (GaussianGammaRealValues.cross_right_data align moved)
    (GaussianGammaFactorialValues.original_C21_factorial r)

private theorem half_square_cross (r x : PTm n) : Γ ⊢[PRAAx] crossEquivalent halfSquareF
    (multiplyF P C) (halfSquareData r) (multiplyData P C x (halfSquareFactor (succ r))) := by
  let N := succ r
  let a := halfData r
  let b := GaussianGammaHalfIntegerValues.valueData N
  let z := GaussianGammaHalfRisingFactorial.factorialValue N
  let y : PTm n := GaussianGammaHalfIntegerValues.baseData
  let S := multiplyF G G
  let c := multiplyData C C z z
  let w := multiplyData G G y y
  let d := halfSquareFactor N
  have ha := half_regular (Γ := Γ) r
  have hb := GaussianGammaHalfIntegerValues.value_regular (Γ := Γ) N
  have hy := GaussianGammaHalfIntegerValues.base_regular (Γ := Γ)
  have hz := constant_regular (Γ := Γ) z
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hd := constant_regular (Γ := Γ) d
  have e := half_factorial_cross (Γ := Γ) r
  have square := multiply_cross G V G V a b a b ha hb ha hb e e
  have split := square_product C G z y hz hy
  have first : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C c d :=
    cross_trans _ _ _ _ _ _ (constant_product_cross z z) (constant_data_cross _ _ (half_square_code N))
  have last : Γ ⊢[PRAAx] crossEquivalent S P w x := GaussianGammaHalfSquareLimit.original_half_square_is_pi x
  have combine := multiply_cross (multiplyF C C) C S P c d w x
    (multiply_fast _ _ _ _ hz hz) hd (multiply_fast _ _ _ _ hy hy) hp first last
  exact cross_trans _ _ _ _ _ _ square (cross_trans _ _ _ _ _ _ split
    (cross_trans _ _ _ _ _ _ combine (multiply_commutative C P d x hd hp)))

theorem wallis_cross (r x : PTm n) : Γ ⊢[PRAAx] crossEquivalent ratioF wallisF (ratioData r) (wallisData r x) := by
  let N := succ r
  let d := halfSquareFactor N
  let t := inverseIntegerDivisor r
  let c := ratioFactor N
  have hd := constant_regular (Γ := Γ) d
  have ht := constant_regular (Γ := Γ) t
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hg := half_regular (Γ := Γ) r
  have first := multiply_cross halfSquareF (multiplyF P C) C C (halfSquareData r) (multiplyData P C x d) t t
    (multiply_fast _ _ _ _ hg hg) (multiply_fast _ _ _ _ hp hd) ht ht (half_square_cross r x) (cross_refl _ _ ht)
  have assoc := multiply_associative P C C x d t hp hd ht
  have code : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C (multiplyData C C d t) c :=
    cross_trans _ _ _ _ _ _ (constant_product_cross d t) (constant_data_cross _ _ (factor_from_products r))
  have cancel := multiply_cross P P (multiplyF C C) C x x (multiplyData C C d t) c hp hp
    (multiply_fast _ _ _ _ hd ht) (constant_regular _) (cross_refl _ _ hp) code
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc cancel)

def integerScaledF : PR 2 := multiplyF C (multiplyF G G)
def integerScaledData (r : PTm n) : PTm n :=
  multiplyData C (multiplyF G G) (naturalPoint (succ r)) (multiplyData G G (integerData r) (integerData r))

theorem integer_divisor_cross (r : PTm n) : Γ ⊢[PRAAx] crossEquivalent integerScaledF C (integerScaledData r)
    (naturalPoint (integerDivisor r)) := by
  let a := integerData r
  let f := fact r
  let c := naturalPoint f
  let d := naturalPoint (f*f)
  let b := naturalPoint (succ r)
  have aR : Γ ⊢[PRAAx] pointCN G a := gamma_regular _ _ (.andI (zero_lt_succ r) (le_refl one))
  have cR := constant_regular (Γ := Γ) c
  have bR := constant_regular (Γ := Γ) b
  have dR := constant_regular (Γ := Γ) d
  have fct := integer_factorial_cross (Γ := Γ) r
  have sq := multiply_cross G C G C a c a c aR cR aR cR fct fct
  have exactSq : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C (multiplyData C C c c) d :=
    cross_trans _ _ _ _ _ _ (constant_product_cross c c)
      (constant_data_cross _ _ (GaussianGammaFactorialValues.natural_product f f))
  have first := multiply_cross C C (multiplyF G G) C b b (multiplyData G G a a) d bR bR
    (multiply_fast _ _ _ _ aR aR) dR (cross_refl _ _ bR) (cross_trans _ _ _ _ _ _ sq exactSq)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (constant_product_cross b d)
      (constant_data_cross _ _ (GaussianGammaFactorialValues.natural_product (succ r) (f*f))))

theorem actual_Stirling_original_Gamma_Wallis_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent ratioF wallisF (ratioData (var 1)) (wallisData (var 1) (var 0)) ⋏
      crossEquivalent integerScaledF C (integerScaledData (var 1)) (naturalPoint (integerDivisor (var 1)))) :=
  closeUniv 2 (.andI (wallis_cross _ _) (integer_divisor_cross _))

end LeanProofs.IPRA.Analysis.GaussianStirlingWallisGammaRatio
