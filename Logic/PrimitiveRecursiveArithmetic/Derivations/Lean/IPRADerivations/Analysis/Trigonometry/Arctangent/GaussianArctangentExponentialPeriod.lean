import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentQuarterExponential
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialAddition
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation

/-!
# The exact period of the named Gaussian exponential

Two applications of the original named exponential addition law turn the
named arctangent quarter turn into a full period.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentExponentialPeriod

open_ipra
open ComplexLogarithmRemainder (code scale eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianArctangentQuarterExponential (quarterF radius quarter_input quarter_cross boundedArguments finiteEstimate original_bounded_arguments)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialAddition (exponential_add_cross)
open GaussianExponentialReference (add_input add_sample finite_reference recode_fixed)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_to_diagonal)
open GaussianNameRingLaws (oneF one_at one_fast multiply_one)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul
  qadd_canonical qadd_represents qmul_canonical qmul_represents represents_congr represents_rescale)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRadiusExponentialName (input inputPrecision index nameF data name_regular sample boundedSamples bounded_samples_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def twiceF : PR 2 := addF quarterF quarterF
def twiceData (z : PTm n) : PTm n := addData z z
def twiceRadius : PTm n := radius+radius
def fullTurnF : PR 2 := addF twiceF twiceF
def fullTurnData (z : PTm n) : PTm n := addData (twiceData z) (twiceData z)
def fullTurnRadius : PTm n := twiceRadius+twiceRadius
def minusOneCode : PTm n := code (ZT.ofNat zero-ZT.ofNat one) (ZT.ofNat zero)
def minusOne : PTm n := ofGaussian minusOneCode one

def twiceImaginary : PTm n := ofGaussian (scale two imaginaryCode) one

private theorem double_gaussian_point (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qadd (ofGaussian a D) (ofGaussian a D) ≐ ofGaussian (scale two a) D := by
  have r := ofGaussian_represents (Γ := Γ) a D hD
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add a a) (scale two a) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ D (qadd_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) e (.eqRefl _) (qadd_represents _ _ _ _ D hD r r))
    (ofGaussian_represents _ _ hD)

theorem half_imaginary_doubled :
    Γ ⊢[PRAAx] qadd (GaussianArctangentQuarterExponential.halfImaginary : PTm n)
      GaussianArctangentQuarterExponential.halfImaginary ≐ imaginaryPoint := by
  have hD : Γ ⊢[PRAAx] le one two := le_succ_self one
  refine (double_gaussian_point imaginaryCode two hD).eqTrans ?_
  exact canonical_unique _ _ _ two (ofGaussian_canonical _ _ hD) (ofGaussian_canonical _ _ (le_refl one))
    hD (ofGaussian_represents _ _ hD)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul two)
      (represents_rescale _ _ one two (ofGaussian_represents _ _ (le_refl one))))

private theorem double_scaled_observation (c d q : PTm n) (h : Γ ⊢[PRAAx] qadd c c ≐ d) :
    Γ ⊢[PRAAx] qadd (qmul c q) (qmul c q) ≐ qmul d q :=
  (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative c q)
    (GaussianRationalPowerAlgebra.qmul_commutative c q)).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add q c c).eqSymm.eqTrans
        ((qmul_congr (.eqRefl _) h).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative q d)))

theorem twice_at (p z : PTm n) : Γ ⊢[PRAAx] ap2 twiceF p (twiceData z) ≐
    qmul imaginaryPoint (ap2 GaussianGammaHalfPiName.nameF (GaussianFastValueCut.exponent two p) z) := by
  have e := GaussianArctangentQuarterExponential.sample_at (Γ := Γ) (GaussianFastValueCut.exponent two p) z
  exact (add_sample quarterF quarterF z z p).eqTrans
    ((qadd_congr e e).eqTrans (double_scaled_observation _ _ _ half_imaginary_doubled))

/-- The full turn's actual sample is twice i times the original π observation at its nested clock. -/
theorem full_turn_at (p z : PTm n) : Γ ⊢[PRAAx] ap2 fullTurnF p (fullTurnData z) ≐
    qmul twiceImaginary (ap2 GaussianGammaHalfPiName.nameF
      (GaussianFastValueCut.exponent two (GaussianFastValueCut.exponent two p)) z) := by
  have e := twice_at (Γ := Γ) (GaussianFastValueCut.exponent two p) z
  exact (add_sample twiceF twiceF (twiceData z) (twiceData z) p).eqTrans
    ((qadd_congr e e).eqTrans
      (double_scaled_observation _ _ _ (double_gaussian_point imaginaryCode one (le_refl one))))

theorem full_turn_input (z : PTm n) (h : Γ ⊢[PRAAx] boundedArguments z) :
    Γ ⊢[PRAAx] input fullTurnF fullTurnRadius (fullTurnData z) := by
  have twice := add_input _ _ radius z z (quarter_input z h) (quarter_input z h)
  exact add_input _ _ twiceRadius (twiceData z) (twiceData z) twice twice

theorem square_gaussian_point (a b : PTm n)
    (he : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.mul a a) b) :
    Γ ⊢[PRAAx] qmul (ofGaussian a one) (ofGaussian a one) ≐ ofGaussian b one := by
  have hr := ofGaussian_represents (Γ := Γ) a one (le_refl one)
  have hs := qmul_represents _ _ a a one one (le_refl _) (le_refl _) hr hr
  exact canonical_unique _ _ _ one (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one))
    (le_refl one) (represents_congr (.eqRefl _) he (one_mul one) hs) (ofGaussian_represents _ _ (le_refl one))

theorem imaginary_square : Γ ⊢[PRAAx] qmul (imaginaryPoint : PTm n) imaginaryPoint ≐ minusOne := by
  apply square_gaussian_point
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [imaginaryCode,minusOneCode,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
      eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

theorem negative_one_square : Γ ⊢[PRAAx] qmul (minusOne : PTm n) minusOne ≐ qone := by
  apply square_gaussian_point
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [minusOneCode,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_one,
      GaussianRootAlgebra.im_one,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

theorem constant_product (a b : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF a b) (qmul a b) := by
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _ ha hb) (constant_regular _)
  refine .allI ?_
  let x := Syn.shift a
  let y := Syn.shift b
  let p : PTm (n+1) := var 0
  have e : Γ.map Fm.shift ⊢[PRAAx]
      ap2 (multiplyF constantF constantF) p (multiplyData constantF constantF x y) ≐ qmul x y :=
    (GaussianNameArithmetic.multiply_at _ _ _ _ _).eqTrans
      ((GaussianNameArithmetic.recode_congr (qmul_congr (constant_at _ _) (constant_at _ _))).eqTrans
        (recode_fixed _ (qmul_canonical _ _)))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,
    GaussianNameArithmetic.subst_multiplyData,GaussianRationalHorner.subst_qmul,x,y,p] using
    e.eqTrans (constant_at p (qmul x y)).eqSymm

theorem constant_cross_congr (a b : PTm n) (he : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] crossEquivalent constantF constantF a b := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (constant_regular _)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] Syn.shift a ≐ Syn.shift b := by
    simpa only [Fm.shift,Fm.subst_eq,Syn.shift] using he.shift
  exact (constant_at _ _).eqTrans (hs.eqTrans (constant_at _ _).eqSymm)

theorem double_exponential_constant (f : PR 2) (R z a b : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hf : Γ ⊢[PRAAx] input f R z)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R z) a)
    (hs : Γ ⊢[PRAAx] qmul a a ≐ b) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (addF f f)) constantF (data (R+R) (addData z z)) b := by
  have hr := name_regular f R z hf
  have ha := constant_regular (Γ := Γ) a
  have hd := cross_to_diagonal _ _ _ _ he
  have prod := GaussianNameArithmetic.multiply_equivalent _ _ _ _ _ _ _ _ hr ha hr ha hd hd
  have exp := cross_symm _ _ _ _ (exponential_add_cross f f R z z hR hf hf)
  have joined := cross_trans _ _ _ _ _ _ exp prod
  have c := cross_trans _ _ _ _ _ _ joined (constant_product a a)
  exact cross_trans _ _ _ _ _ _ c (constant_cross_congr _ _ hs)

theorem full_turn_cross (z : PTm n) (h : Γ ⊢[PRAAx] boundedArguments z)
    (C : PTm n) (hf : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent (nameF fullTurnF) constantF
      (data fullTurnRadius (fullTurnData z)) qone := by
  have hq := quarter_input z h
  have r : Γ ⊢[PRAAx] le one (radius : PTm n) := le_succ_self one
  have r2 : Γ ⊢[PRAAx] le one (twiceRadius : PTm n) := le_trans r (le_add_right _ _)
  have half := double_exponential_constant quarterF radius z imaginaryPoint minusOne r hq
    (quarter_cross z C h hf) imaginary_square
  exact double_exponential_constant twiceF twiceRadius (twiceData z) minusOne qone r2
    (add_input _ _ radius z z hq hq) half negative_one_square

theorem original_full_turn_input (z : PTm n) : Γ ⊢[PRAAx] input fullTurnF fullTurnRadius (fullTurnData z) :=
  full_turn_input z (original_bounded_arguments z)

theorem original_full_turn_cross (z C : PTm n) (hf : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent (nameF fullTurnF) constantF
      (data fullTurnRadius (fullTurnData z)) qone :=
  full_turn_cross z (original_bounded_arguments z) C hf

theorem enlarge_input (f : PR 2) (R S x : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hRS : Γ ⊢[PRAAx] le R S) : Γ ⊢[PRAAx] input f S x := by
  refine .andI h.andE₁ (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] boundedSamples f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_boundedSamples,Syn.shift] using h.andE₂.shift
  have hRS' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift R) (Syn.shift S) := by
    simpa [Fm.shift,Syn.shift] using hRS.shift
  exact bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hRS')
    (bounded_samples_at _ _ _ (var 0) hs)

/-- Compare the two original clocks through a common later finite sum. -/
theorem same_exp_different_radius_at (f : PR 2) (R S x p : PTm n)
    (hR : Γ ⊢[PRAAx] input f R x) (hS : Γ ⊢[PRAAx] input f S x) :
    Γ ⊢[PRAAx] distanceBounded (sample f R p x) (sample f S p x) (one+one) (unit p) := by
  let j := inputPrecision R p+inputPrecision S p
  let K := index R p+index S p
  have left := finite_reference f R x p j K hR (le_add_right _ _) (le_add_right _ _)
  have right := finite_reference f S x p j K hS (le_add_left _ _) (le_add_left _ _)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_symmetric _ _ _ _ (unit_positive p) left) right

theorem same_exp_different_radius (f : PR 2) (R S x : PTm n)
    (hR : Γ ⊢[PRAAx] input f R x) (hS : Γ ⊢[PRAAx] input f S x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data R x) (data S x) := by
  apply cross_of_diagonal_rate _ _ _ _ (one+one) (name_regular f R x hR) (name_regular f S x hS)
  refine .allI ?_
  have hR' : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_input,Syn.shift] using hR.shift
  have hS' : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift S) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_input,Syn.shift] using hS.shift
  simpa only [diagonalRate,GaussianRadiusExponentialName.subst_data,Syn.shift,PTm.subst_add,
    PTm.subst_succ,PTm.subst_zero,sample] using
    same_exp_different_radius_at f (Syn.shift R) (Syn.shift S) (Syn.shift x) (var 0) hR' hS'

theorem constant_one_cross (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalReciprocal.subst_qone] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) (qone : PTm (n+1))).eqTrans
      (one_at (var 0) (Syn.shift x)).eqSymm

def translationRadius (R : PTm n) : PTm n := (R+fullTurnRadius)+(R+fullTurnRadius)

/-- Translating any bounded Gaussian name by the full arctangent turn preserves the exponential. -/
theorem full_turn_translation (f : PR 2) (R x z C : PTm n) (hx : Γ ⊢[PRAAx] input f R x)
    (hf : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (addF f fullTurnF)) (nameF f)
      (data (translationRadius R) (addData x (fullTurnData z))) (data R x) := by
  let S := R+fullTurnRadius
  let t := fullTurnData z
  let F := nameF f
  let a := data S x
  let b := data S t
  have hsmall := original_full_turn_input (Γ := Γ) z
  have hS : Γ ⊢[PRAAx] le one S := by
    have hR : Γ ⊢[PRAAx] le one (radius : PTm n) := le_succ_self one
    exact le_trans (le_trans (le_trans hR (le_add_right _ _)) (le_add_right _ _)) (le_add_left _ _)
  have hleft := enlarge_input f R S x hx (le_add_right _ _)
  have hright := enlarge_input fullTurnF fullTurnRadius S t hsmall (le_add_left _ _)
  have hreg := name_regular f S x hleft
  have hturn := cross_trans _ _ _ _ _ _
    (same_exp_different_radius fullTurnF S fullTurnRadius t hright hsmall)
    (original_full_turn_cross z C hf)
  have hidentity := cross_trans _ _ _ _ _ _ hturn (constant_one_cross a)
  have hprod := GaussianNameArithmetic.multiply_equivalent F F (nameF fullTurnF) oneF a a b a hreg hreg
    (name_regular _ _ _ hright) (one_fast a) (cross_to_diagonal _ _ _ _ (cross_refl _ _ hreg))
    (cross_to_diagonal _ _ _ _ hidentity)
  have first := cross_symm _ _ _ _ (exponential_add_cross f fullTurnF S x t hS hleft hright)
  have drop := cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ first hprod) (multiply_one F a hreg)
  exact cross_trans _ _ _ _ _ _ drop (same_exp_different_radius f S R x hleft hx)

end LeanProofs.IPRA.Analysis.GaussianArctangentExponentialPeriod
