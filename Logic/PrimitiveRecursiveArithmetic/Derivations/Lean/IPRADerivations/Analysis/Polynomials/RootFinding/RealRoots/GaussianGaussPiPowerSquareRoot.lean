import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussIndependentSquareRoot
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Normalization.GaussianGaussMultiplicationHalfPower
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedProductSquare

/-!
# Independent sampling of the positive Gauss half-power of doubled π

The program reads the actual finite family power ((2pi)^N).
At (m=N+1), its value times the named (m^{-1/2}) is the original
Gauss reference product. The comparison uses the certified positive
reference product times (m,m^{-1/2}) as a square-root witness.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGaussPiPowerSquareRoot

open_ipra
open GaussianGammaGaussReferenceSquare (doubledPiBody doubledPiPowerF doubledPiPowerData
  normalizationF normalizationData)
open GaussianGammaGaussIndependentSquareRoot (doubled_power_nonnegative reciprocal_fraction positive_reference_observations)
open GaussianGammaGaussReflectionPowerConstant (reciprocalModulus)
open GaussianGaussMultiplicationHalfPower (halfData half_regular half_square half_sample_canonical half_sample_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNamedBoundedSquareRoot (observations observation_at sqrtF square_root_cross)
open GaussianNamedProductSquare (square_product right_unit)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast multiply_canonical)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalNonnegativeFractions (fraction_nonnegative nonnegative_of_positive multiply_nonnegative_at)
open GaussianRationalNonnegativeProducts (nonnegative)
open GaussianRationalHorner (canonical qmul)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalReciprocal (qone)
open GaussianCyclicSineProductSquare (data)
open ComplexLogarithmRemainder (scale oneCode mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "A" => GaussianGammaGaussPositiveReference.nameF
local notation "H" => GaussianGaussMultiplicationHalfPower.halfF
local notation "C" => constantF
local notation "D" => doubledPiPowerF
local notation "M" N:arg => naturalPoint (succ N)
local notation "I" N:arg => fraction one (succ N)

private theorem reciprocal_unit (N : PTm n) : Γ ⊢[PRAAx] qmul (M N) (I N) ≐ qone := by
  let m := succ N
  let a := scale m oneCode
  let b : PTm n := scale one oneCode
  have hm := zero_lt_succ (Γ := Γ) N
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul a b) a := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp [a,b,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
  apply GaussianRationalHorner.canonical_unique _ _ a m (GaussianRationalHorner.qmul_canonical _ _)
    GaussianRationalSyntheticDivision.qone_canonical hm
  · apply GaussianRationalHorner.represents_congr (.eqRefl _) e (one_mul m)
    exact GaussianRationalHorner.qmul_represents _ _ a b one m (le_refl one) hm
      (GaussianRationalNaturalScale.natural_point_represents m) (GaussianRationalHorner.ofGaussian_represents _ _ hm)
  · exact GaussianRationalReciprocal.qone_represents_scaled m

private theorem constants_cancel (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C
    (multiplyData C C (M N) (I N)) (qone : PTm n) :=
  cross_trans _ _ _ _ _ _ (constant_product_cross (M N) (I N))
    (constant_data_cross _ _ (reciprocal_unit N))

private theorem constants_cancel_reverse (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C
    (multiplyData C C (reciprocalModulus N) (M N)) (qone : PTm n) := by
  let a := M N
  let b := I N
  let c := reciprocalModulus N
  have e := (GaussianRationalPowerAlgebra.qmul_commutative (Γ := Γ) c a).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (reciprocal_fraction N).eqSymm).eqTrans (reciprocal_unit N))
  exact cross_trans _ _ _ _ _ _ (constant_product_cross c a) (constant_data_cross _ _ e)

def scaleF : PR 2 := multiplyF C H
def scaleData (N : PTm n) : PTm n := multiplyData C H (M N) (halfData (succ N))

private theorem scale_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN scaleF (scaleData N) :=
  multiply_fast C H _ _ (constant_regular _) (half_regular _ (zero_lt_succ N))

private theorem scale_times_half (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF scaleF H) C
    (multiplyData scaleF H (scaleData N) (halfData (succ N))) qone := by
  let m := succ N
  let x := halfData m
  let y := I N
  let h := half_regular (Γ := Γ) m (zero_lt_succ N)
  let c := constant_regular (Γ := Γ) (M N)
  have e := multiply_associative C H H (M N) x x c h h
  have f := multiply_cross C C (multiplyF H H) C (M N) (M N)
    (multiplyData H H x x) y c c (multiply_fast _ _ _ _ h h) (constant_regular y)
    (cross_refl _ _ c) (half_square m (zero_lt_succ N))
  exact cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _ f (constants_cancel N))

private theorem scale_square (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF scaleF scaleF) C
    (multiplyData scaleF scaleF (scaleData N) (scaleData N)) (M N) := by
  let m := succ N
  let a := M N
  let b := I N
  let x := halfData m
  let y := multiplyData H H x x
  let U := multiplyF C C
  let u := multiplyData C C a a
  let v := multiplyData C C a b
  have h := half_regular (Γ := Γ) m (zero_lt_succ N)
  have ca := constant_regular (Γ := Γ) a
  have cb := constant_regular (Γ := Γ) b
  have cu := multiply_fast C C a a ca ca
  have split := square_product C H a x ca h
  have e := multiply_cross U U (multiplyF H H) C u u y b cu cu (multiply_fast _ _ _ _ h h)
    cb (cross_refl _ _ cu) (half_square m (zero_lt_succ N))
  have assoc := multiply_associative C C C a a b ca ca cb
  have cancel := multiply_cross C C U C a a v qone ca ca
    (multiply_fast C C a b ca cb) (constant_regular _) (cross_refl _ _ ca) (constants_cancel N)
  exact cross_trans _ _ _ _ _ _ split
    (cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _ assoc
      (cross_trans _ _ _ _ _ _ cancel (right_unit C a ca))))

def witnessF : PR 2 := multiplyF A scaleF
def witnessData (N x : PTm n) : PTm n :=
  multiplyData A scaleF (GaussianGammaGaussPositiveReference.nameData N x) (scaleData N)

private theorem witness_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN witnessF (witnessData N x) :=
  multiply_fast A scaleF _ _ (GaussianGammaGaussPositiveReference.name_regular N x) (scale_regular N)

private theorem witness_square (N x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF witnessF witnessF) D
    (multiplyData witnessF witnessF (witnessData N x) (witnessData N x)) (doubledPiPowerData N x) := by
  let a := GaussianGammaGaussPositiveReference.nameData N x
  let b := scaleData N
  let p := doubledPiPowerData N x
  let m := M N
  let i := reciprocalModulus N
  let u := multiplyData A A a a
  let v := multiplyData scaleF scaleF b b
  let c := multiplyData C C i m
  have ha := GaussianGammaGaussPositiveReference.name_regular (Γ := Γ) N x
  have hb := scale_regular (Γ := Γ) N
  have hm := constant_regular (Γ := Γ) m
  have hi := constant_regular (Γ := Γ) i
  have root := GaussianGammaGaussPositiveReference.square_normalization (Γ := Γ) N x
  have hp : Γ ⊢[PRAAx] pointCN D p :=
    GaussianNamedFiniteProductFamily.family_product_regular _ _ _ _
      (GaussianNamedFiniteProductFamilyAlgebra.multiply_regular _ _ _ _ _ _
        (GaussianGammaGaussReflectionFamily.pi_rows N x)
        (GaussianGammaGaussReflectionPowerConstant.two_rows N (data N x)))
  have hn := multiply_fast D C p i hp hi
  have e := multiply_cross (multiplyF A A) normalizationF (multiplyF scaleF scaleF) C
    u (normalizationData N x) v m (multiply_fast _ _ _ _ ha ha) hn
    (multiply_fast _ _ _ _ hb hb) hm root (scale_square N)
  have assoc := multiply_associative D C C p i m hp hi hm
  have cancel := multiply_cross D D (multiplyF C C) C p p c qone hp hp
    (multiply_fast C C i m hi hm) (constant_regular _) (cross_refl _ _ hp) (constants_cancel_reverse N)
  exact cross_trans _ _ _ _ _ _ (square_product A scaleF a b ha hb)
    (cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _ assoc
      (cross_trans _ _ _ _ _ _ cancel (right_unit D p hp))))

private theorem scale_nonnegative (N p : PTm n) : Γ ⊢[PRAAx] nonnegative (ap2 scaleF p (scaleData N)) := by
  let a := M N
  let b := halfData (succ N)
  let r := GaussianFastValueCut.exponent (multiplyModulus C H a b) p
  exact multiply_nonnegative_at C H a b p
    (GaussianRationalNonnegativeProducts.congr (constant_at r a).eqSymm (fraction_nonnegative (succ N) one (le_refl one)))
    (nonnegative_of_positive _ (half_sample_canonical _ r) (half_sample_positive _ r))

private theorem witness_observation (p N x : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 witnessF p (witnessData N x)) ⋏ nonnegative (ap2 witnessF p (witnessData N x)) := by
  let a := GaussianGammaGaussPositiveReference.nameData N x
  let b := scaleData N
  let r := GaussianFastValueCut.exponent (multiplyModulus A scaleF a b) p
  exact .andI (multiply_canonical A scaleF a b p)
    (multiply_nonnegative_at A scaleF a b p
      (GaussianGammaGaussPositiveReference.nonnegative_at r N x) (scale_nonnegative N r))

private theorem witness_observations (N x : PTm n) : Γ ⊢[PRAAx] observations witnessF (witnessData N x) := by
  refine .allI ?_
  have e : Syn.shift (witnessData N x) = witnessData (Syn.shift N) (Syn.shift x) := by
    simp [witnessData,scaleData,one,Syn.shift]
  rw [e]
  exact witness_observation (var 0) (Syn.shift N) (Syn.shift x)

private theorem doubled_observation (p N x : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 D p (doubledPiPowerData N x)) ⋏ nonnegative (ap2 D p (doubledPiPowerData N x)) := by
  let F := multiplyF GaussianGammaHalfPiName.nameF C
  let f := GaussianNamedFiniteProductFamily.rowF F doubledPiBody
  let R := GaussianNamedFiniteProductFamily.radius F doubledPiBody N (data N x)
  let t := GaussianNamedFiniteProductName.clock N R one p
  exact .andI (GaussianRationalHorner.canonical_congr (GaussianNamedFiniteProductName.name_at f p N R one (data N x))
    (GaussianNamedFiniteProduct.sample_canonical f t N (data N x))) (doubled_power_nonnegative p N x)

private theorem doubled_observations (N x : PTm n) : Γ ⊢[PRAAx] observations D (doubledPiPowerData N x) := by
  refine .allI ?_
  have e : Syn.shift (doubledPiPowerData N x) = doubledPiPowerData (Syn.shift N) (Syn.shift x) := by
    simp [doubledPiPowerData,GaussianNamedFiniteProductFamily.productData,one,Syn.shift]
  rw [e]
  exact doubled_observation (var 0) (Syn.shift N) (Syn.shift x)

def nameF : PR 2 := sqrtF D
def nameData (N x : PTm n) : PTm n := doubledPiPowerData N x

theorem witness_cross (N x : PTm n) : Γ ⊢[PRAAx] crossEquivalent witnessF nameF (witnessData N x) (nameData N x) :=
  square_root_cross _ _ _ _ (witness_regular N x) (witness_observations N x) (doubled_observations N x) (witness_square N x)

theorem name_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN nameF (nameData N x) := by
  have e := witness_cross (Γ := Γ) N x
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e) e

theorem name_square (N x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF nameF nameF) D
    (multiplyData nameF nameF (nameData N x) (nameData N x)) (doubledPiPowerData N x) := by
  have a := name_regular (Γ := Γ) N x
  have b := witness_regular (Γ := Γ) N x
  have c := cross_symm _ _ _ _ (witness_cross (Γ := Γ) N x)
  exact cross_trans _ _ _ _ _ _ (multiply_cross nameF witnessF nameF witnessF
    (nameData N x) (witnessData N x) (nameData N x) (witnessData N x) a b a b c c)
    (witness_square N x)

theorem sample_nonnegative (p N x : PTm n) : Γ ⊢[PRAAx] nonnegative (ap2 nameF p (nameData N x)) :=
  GaussianRationalNonnegativeProducts.congr (GaussianNamedBoundedSquareRoot.sample_at D p (nameData N x)).eqSymm
    (fraction_nonnegative _ _ (GaussianCoefficientNameBounds.unit_positive _))

theorem reference_cross (N x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (multiplyF nameF H)
    GaussianGammaGaussReferenceProduct.nameF (multiplyData nameF H (nameData N x) (halfData (succ N)))
    (GaussianGammaGaussReferenceProduct.data (succ N)) := by
  let a := GaussianGammaGaussPositiveReference.nameData N x
  let b := scaleData N
  let h := halfData (succ N)
  let v := multiplyData scaleF H b h
  have hA := GaussianGammaGaussPositiveReference.name_regular (Γ := Γ) N x
  have hB := scale_regular (Γ := Γ) N
  have hH := half_regular (Γ := Γ) (succ N) (zero_lt_succ N)
  have first := multiply_cross nameF witnessF H H (nameData N x) (witnessData N x) h h
    (name_regular N x) (witness_regular N x) hH hH (cross_symm _ _ _ _ (witness_cross N x)) (cross_refl _ _ hH)
  have assoc := multiply_associative A scaleF H a b h hA hB hH
  have cancel := multiply_cross A A (multiplyF scaleF H) C a a v qone hA hA
    (multiply_fast _ _ _ _ hB hH) (constant_regular _) (cross_refl _ _ hA) (scale_times_half N)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ cancel (cross_trans _ _ _ _ _ _ (right_unit A a hA)
      (cross_symm _ _ _ _ (GaussianGammaGaussPositiveReference.original_cross N x)))))

theorem actual_Gauss_reference_through_pi_half_power_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent (multiplyF nameF H) GaussianGammaGaussReferenceProduct.nameF
        (multiplyData nameF H (nameData (var 1) (var 0)) (halfData (succ (var 1))))
        (GaussianGammaGaussReferenceProduct.data (succ (var 1)))) :=
  closeUniv 2 (reference_cross _ _)

end LeanProofs.IPRA.Analysis.GaussianGaussPiPowerSquareRoot
