import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.GaussianGaussDuplication
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Gamma.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.Gamma.GaussianGammaInputProperness

/-!
# Positive rational arguments in the original Gauss duplication
The proof binds each of the literal Gauss rows to the corresponding
positive rational Gamma data used by the Stirling logarithm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingNativeDuplication

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaInputProperness (gamma_source_equal original_Gamma_proper)
open GaussianGammaReciprocalInverse (gammaF gammaHeight original_gamma_inverse)
open GaussianGammaRadiusOverlap (original_Gamma_overlap)
open GaussianGaussExplicitShiftedProducts (gammaRowData gamma_row_regular twoRowsF twoRowsData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_to_diagonal cross_trans)
open GaussianRationalHorner (positive_product)
open GaussianRootAlgebra (equal equal_of_values equal_symm re_add im_add re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_source gamma_source_at_radius gamma_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "gd" => GaussianGammaReciprocalInverse.gammaData
local notation "P" => GaussianGammaC7Name.nameF
local notation "pd" => GaussianGammaC7Name.data

theorem scale_argument (a E : PTm n) : Γ ⊢[PRAAx] equal (scale E (arg a)) (arg (E*a)) := by
  apply equal_of_values <;> simp only [arg,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

theorem gamma_rescale (a b E : PTm n) (hs : Γ ⊢[PRAAx] source a b) (he : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (gammaData (E*a) (E*b)) (gammaData a b) := by
  let v := arg (E*a)
  let z := arg a
  let w := scale E z
  let D := E*b
  have hpos : Γ ⊢[PRAAx] source (E*a) D :=
    .andI (positive_product _ _ he hs.andE₁) (positive_product _ _ he hs.andE₂)
  have disk : Γ ⊢[PRAAx] le (E*a) (a*D) := by
    unfold D
    ipra_le 𝔞 E*𝔞 a*sl hs.andE₂
  have vsrc := gamma_source_at_radius (E*a) D a hpos hs.andE₁ disk
  have e := scale_argument (Γ := Γ) a E
  have wsrc := gamma_source_equal v w a D one D vsrc (equal_symm e)
  have orig := gamma_source a b hs
  have wInput := (original_gamma_inverse w a D one D wsrc).andE₁
  have zInput := (original_gamma_inverse z a b one b orig).andE₁
  have eq := GaussianGammaEncodingRescaling.original_C7_rescale z a b E orig.andE₁ he
  have names := GaussianNameReciprocal.names_equivalent P P (gammaHeight w a D D) (gammaHeight z a b b)
    (pd w a D) (pd z a b) wInput.andE₁ zInput.andE₁ wInput.andE₂ zInput.andE₂ (cross_to_diagonal _ _ _ _ eq)
  have overlap := original_Gamma_overlap v (E*a) a D one D one D (gamma_source (E*a) D hpos) vsrc
  exact cross_trans _ _ _ _ _ _ overlap (cross_trans _ _ _ _ _ _
    (original_Gamma_proper v w a D one D vsrc (equal_symm e)) names)

theorem gauss_source (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianGammaGaussShiftedProduct.source (arg a) a b two one b := by
  let R := scaledRadius a two
  have twoPos : Γ ⊢[PRAAx] le one two := le_succ_self one
  have h : Γ ⊢[PRAAx] le one R := positive_product _ _ twoPos
    (le_trans hs.andE₁ (le_add_right a two))
  have disk : Γ ⊢[PRAAx] le (two*a) (R*b) := by
    unfold R scaledRadius
    ipra_le 2*𝔞 a*sl hs.andE₂ + 4*𝔞 b
  have src := gamma_source_at_radius (two*a) b R (.andI (positive_product _ _ twoPos hs.andE₁) hs.andE₂) h disk
  exact .andI (.andI twoPos (GaussianStirlingGammaLogarithm.native_disk a b hs))
    (gamma_source_equal _ _ _ _ _ _ src (equal_symm (scale_argument a two)))

private theorem row_argument (r a b : PTm n) : Γ ⊢[PRAAx]
    equal (shiftedNumerator (arg a) b two r) (arg (two*a+b*r)) := by
  apply equal_of_values <;>
    simp only [shiftedNumerator,translated,arg,re_add,im_add,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem row_cross (r a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hr : Γ ⊢[PRAAx] lt r two) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (gammaRowData r (arg a) a b two b)
      (gammaData (two*a+b*r) (b*two)) := by
  let w := shiftedNumerator (arg a) b two r
  let z := arg (two*a+b*r)
  let D := b*two
  have row := GaussianGammaGaussShiftedProduct.row_source (arg a) a b two r one b (gauss_source a b hs) hr
  have e := row_argument (Γ := Γ) r a b
  have v := gamma_source_equal w z (a+one) D one D row e
  have h0 := positive_product two a (le_succ_self one) hs.andE₁
  have h : Γ ⊢[PRAAx] source (two*a+b*r) D :=
    .andI (le_trans h0 (le_add_right _ _)) (positive_product _ _ hs.andE₂ (le_succ_self one))
  have moved := original_Gamma_proper w z (a+one) D one D row e
  exact cross_trans _ _ _ _ _ _ moved (original_Gamma_overlap z (a+one) (two*a+b*r) D one D one D v (gamma_source _ _ h))


def halfNumerator (a b : PTm n) : PTm n := two*a+b
def halfDenominator (b : PTm n) : PTm n := b*two

theorem half_source (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] source (halfNumerator a b) (halfDenominator b) :=
  .andI (le_trans (positive_product _ _ (le_succ_self one) hs.andE₁) (le_add_right _ _))
    (positive_product _ _ hs.andE₂ (le_succ_self one))

private theorem data_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] gammaData a b ≐ gammaData c d := by
  simpa only [GaussianStirlingGammaLogarithm.subst_gammaData,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (gammaData (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

theorem half_encoding : Γ ⊢[PRAAx]
    crossEquivalent gammaF gammaF (gammaData one two) (GaussianGammaHalfSquareLimit.gammaHalf : PTm n) := by
  have source : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (arg one) one two one two :=
    gamma_source _ _ (.andI (le_refl one) (le_succ_self one))
  have h : Γ ⊢[PRAAx] equal (arg one) oneCode := by
    apply equal_of_values <;> simp [arg,one]
  exact original_Gamma_proper _ _ _ _ _ _ source h

private theorem first_row (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (gammaRowData zero (arg a) a b two b) (gammaData a b) := by
  have e := data_congr (Γ := Γ) (a := two*a+b*zero) (c := two*a) (by ipra_ring) (mul_comm b two)
  have next := GaussianGammaCompactCutoffAlignment.cross_data_congr gammaF gammaF _ _ _ _ (.eqRefl _) e
    (row_cross zero a b hs (le_succ_self one))
  exact cross_trans _ _ _ _ _ _ next (gamma_rescale a b two hs (le_succ_self one))

private theorem second_row (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (gammaRowData one (arg a) a b two b)
      (gammaData (halfNumerator a b) (halfDenominator b)) := by
  have e := data_congr (Γ := Γ) (a := two*a+b*one) (c := halfNumerator a b) (by unfold halfNumerator; ipra_ring)
    (.eqRefl (b*two))
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr gammaF gammaF _ _ _ _ (.eqRefl _) e
    (row_cross one a b hs (le_refl two))

theorem double_source (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] source (two*a) b :=
  .andI (positive_product _ _ (le_succ_self one) hs.andE₁) hs.andE₂

theorem doubled_gamma (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (GaussianGaussMultiplicationCofinalRows.scaledData (arg a) a b two b)
      (gammaData (two*a) b) := by
  let z := scale two (arg a)
  let v := arg (two*a)
  let R := scaledRadius a two
  have e := scale_argument (Γ := Γ) a (two : PTm n)
  have h := (gauss_source a b hs).andE₂
  have hV := gamma_source_equal z v R b one b h e
  exact cross_trans _ _ _ _ _ _ (original_Gamma_proper z v R b one b h e)
    (original_Gamma_overlap v R (two*a) b one b one b hV (gamma_source _ _ (double_source a b hs)))

open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)

abbrev leftF : PR 2 := multiplyF gammaF gammaF
def leftData (a b : PTm n) : PTm n := multiplyData gammaF gammaF (gammaData a b)
  (gammaData (halfNumerator a b) (halfDenominator b))
abbrev rightF : PR 2 := multiplyF (multiplyF powerF gammaF) gammaF
def rightData (a b : PTm n) : PTm n :=
  multiplyData (multiplyF powerF gammaF) gammaF
    (multiplyData powerF gammaF (limitData (arg a) a b two) (gammaData one two)) (gammaData (two*a) b)

set_option maxHeartbeats 1400000 in
theorem native_duplication (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData a b) (rightData a b) := by
  let z := arg a
  let R := a
  let k : PTm n := zero
  let y := gammaData a b
  let v := gammaData (halfNumerator a b) (halfDenominator b)
  let u := gammaData (two*a) b
  let w : PTm n := gammaData one two
  let g := GaussianGaussMultiplicationCofinalRows.scaledData z R b two b
  let s := gammaRowData zero z R b two b
  let t := gammaRowData one z R b two b
  let p := limitData z R b two
  let S := GaussianGammaHalfSqrtPi.nameF
  have h := gauss_source a b hs
  have h0 := gamma_row_regular zero z R b two one b h (le_succ_self one)
  have h1 := gamma_row_regular one z R b two one b h (le_refl two)
  have e := multiply_cross gammaF gammaF gammaF gammaF s y t v h0 (gamma_regular a b hs)
    h1 (gamma_regular _ _ (half_source a b hs)) (first_row a b hs) (second_row a b hs)
  have pg := GaussianGaussMultiplicationCofinalRows.limit_power_regular z R b two one b h
  have gg := GaussianGaussMultiplicationCofinalRows.scaled_regular z R b two one b h
  have hsqrt := GaussianGammaHalfSqrtPi.original_half_is_sqrt_pi (Γ := Γ) k
  have kReg := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ hsqrt) hsqrt
  have wReg := gamma_regular (Γ := Γ) one two (.andI (le_refl one) (le_succ_self one))
  have atHalf := cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ (half_encoding (Γ := Γ)) hsqrt)
  have coeff := multiply_cross powerF powerF S gammaF p p k w pg pg kReg wReg (cross_refl _ _ pg) atHalf
  have right := multiply_cross (multiplyF powerF S) (multiplyF powerF gammaF) gammaF gammaF
    (multiplyData powerF S p k) (multiplyData powerF gammaF p w) g u
    (multiply_fast _ _ _ _ pg kReg) (multiply_fast _ _ _ _ pg wReg)
    gg (gamma_regular _ _ (double_source a b hs)) coeff (doubled_gamma a b hs)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e)
    (cross_trans _ _ _ _ _ _ (GaussianGaussDuplication.duplication z R b one b k h) right)

end LeanProofs.IPRA.Analysis.GaussianStirlingNativeDuplication
