import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaEulerReflectionLimit
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShift

/-!
# Cleared reflection of the original pole-free Gamma names

For the two original values at z/B and −z/B, the scaled literal sine
product is their multiplicative inverse. The domain is exactly the
conjunction of the original pole-free certificates at the two arguments.
The original Gamma shift then gives the complementary-argument
identity with z/B times the same product.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaReflectionProduct

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerReflectionLimit (pairF pairData scaledF scaledData original_reciprocal_reflection_product)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular gamma_product inverse_pairs named_product_exchange)
open GaussianGammaEulerReflectionHead (paired_argument negativeSquare)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF multiply_associative multiply_commutative)
open GaussianRationalHorner (ofGaussian)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "H" => GaussianGammaC7Name.nameF
local notation "D" => GaussianGammaC7Name.data
local notation "S" => GaussianSineProductName.nameF
local notation "shifted" => GaussianGammaEulerHeadShift.shifted

def source (z R B a d : PTm n) : Fm PTm n :=
  GaussianGammaReciprocalInverse.source z R B a d ⋏
    GaussianGammaReciprocalInverse.source (gneg z) R B a d

def gammaPairF : PR 2 := multiplyF gammaF gammaF
def gammaPairData (z R B d : PTm n) : PTm n :=
  multiplyData gammaF gammaF (gammaData z R B d) (gammaData (gneg z) R B d)

theorem actual_Gamma_reflection_product (z R B a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF scaledF gammaPairF) oneF
      (multiplyData scaledF gammaPairF (scaledData z R B) (gammaPairData z R B d)) (D z R B) := by
  let X := D z R B
  let Y := D (gneg z) R B
  let A := gammaData z R B d
  let B' := gammaData (gneg z) R B d
  let G := gammaPairF
  let u := gammaPairData z R B d
  have hx := GaussianGammaC7Name.name_regular z R B hs.andE₁.andE₁
  have hy := GaussianGammaC7Name.name_regular (gneg z) R B hs.andE₂.andE₁
  have ha := gamma_regular z R B a d hs.andE₁
  have hb := gamma_regular (gneg z) R B a d hs.andE₂
  have hg := multiply_fast gammaF gammaF A B' ha hb
  have hprod := original_reciprocal_reflection_product z R B hs.andE₁.andE₁
  have scaled : Γ ⊢[PRAAx] pointCN scaledF (scaledData z R B) := multiply_fast constantF S
    (negativeSquare z B) (GaussianSineProductName.data z R B) (constant_regular (negativeSquare z B))
    (GaussianSineProductName.name_regular z R B hs.andE₁.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₂)
  have refl := multiply_cross scaledF pairF G G (scaledData z R B) (pairData z R B) u u
    scaled (multiply_fast _ _ _ _ hx hy) hg hg (cross_symm _ _ _ _ hprod) (cross_refl _ _ hg)
  have p := gamma_product z R B a d hs.andE₁
  have q := cross_trans _ _ _ _ _ _ (gamma_product (gneg z) R B a d hs.andE₂)
    (GaussianBoundedInverseApartness.ones_equivalent Y X)
  exact cross_trans _ _ _ _ _ _ refl (inverse_pairs H H gammaF gammaF X Y A B' X hx hy ha hb p q)

def complementarySource (z R B a d e f : PTm n) : Fm PTm n :=
  GaussianGammaReciprocalInverse.source z R B a d ⋏ GaussianGammaShift.input (gneg z) R B a d e f

def productLinearF : PR 2 := multiplyF constantF S
def productLinearData (z R B : PTm n) : PTm n :=
  multiplyData constantF S (ofGaussian z B) (GaussianSineProductName.data z R B)
def complementaryData (z R B d f : PTm n) : PTm n :=
  multiplyData gammaF gammaF (gammaData z R B d) (gammaData (shifted (gneg z) B) (R+one) B f)

theorem complementary_product (z R B a d e f : PTm n) (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF productLinearF gammaPairF) oneF
      (multiplyData productLinearF gammaPairF (productLinearData z R B) (complementaryData z R B d f)) (D z R B) := by
  let C := constantF
  let G := gammaF
  let x := ofGaussian z B
  let y := ofGaussian (gneg z) B
  let A := gammaData z R B d
  let B' := gammaData (gneg z) R B d
  let T := gammaData (shifted (gneg z) B) (R+one) B f
  let s := GaussianSineProductName.data z R B
  let AB := gammaPairData z R B d
  let YB := multiplyData C G y B'
  let YA := multiplyData C G y A
  let q := productLinearData z R B
  have hB := hs.andE₁.andE₁.andE₂.andE₁
  have hx := constant_regular (Γ := Γ) x
  have hy := constant_regular (Γ := Γ) y
  have hA := gamma_regular z R B a d hs.andE₁
  have hB' := gamma_regular (gneg z) R B a d hs.andE₂.andE₁
  have hT := gamma_regular _ _ _ _ _ (GaussianGammaShift.shifted_source (gneg z) R B a d e f hs.andE₂)
  have hAB := multiply_fast G G A B' hA hB'
  have hYB := multiply_fast C G y B' hy hB'
  have hYA := multiply_fast C G y A hy hA
  have hS := GaussianSineProductName.name_regular z R B hB hs.andE₁.andE₁.andE₂.andE₂
  have ht := GaussianGammaShift.C21_Gamma_shift (gneg z) R B a d e f hs.andE₂
  have liftShift := multiply_cross G G G (multiplyF C G) A A T YB hA hA hT hYB (cross_refl _ _ hA) ht
  have swap := multiply_cross (multiplyF G C) (multiplyF C G) G G (multiplyData G C A y) YA B' B'
    (multiply_fast _ _ _ _ hA hy) hYA hB' hB' (multiply_commutative G C A y hA hy) (cross_refl _ _ hB')
  have reordered := cross_trans _ _ _ _ _ _ liftShift
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative G C G A y B' hA hy hB'))
      (cross_trans _ _ _ _ _ _ swap (multiply_associative C G G y A B' hy hA hB')))
  have hq := multiply_fast C S x s hx hS
  have start := multiply_cross productLinearF productLinearF gammaPairF (multiplyF C gammaPairF)
    q q (complementaryData z R B d f) (multiplyData C gammaPairF y AB) hq hq
    (multiply_fast _ _ _ _ hA hT) (multiply_fast _ _ _ _ hy hAB) (cross_refl _ _ hq) reordered
  have exchange := named_product_exchange C S C gammaPairF x s y AB hx hS hy hAB
  let value := negativeSquare z B
  have xy : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C (multiplyData C C x y) value :=
    cross_trans _ _ _ _ _ _ (constant_product_cross x y)
    (constant_data_cross _ _ (paired_argument z B hB))
  have replace := multiply_cross (multiplyF C C) C S S (multiplyData C C x y) value s s
    (multiply_fast _ _ _ _ hx hy) (constant_regular _) hS hS xy (cross_refl _ _ hS)
  have bind := multiply_cross (multiplyF (multiplyF C C) S) scaledF gammaPairF gammaPairF
    (multiplyData (multiplyF C C) S (multiplyData C C x y) s) (scaledData z R B) AB AB
    (multiply_fast _ _ _ _ (multiply_fast _ _ _ _ hx hy) hS) (multiply_fast _ _ _ _ (constant_regular value) hS)
    hAB hAB replace (cross_refl _ _ hAB)
  have rebracket := cross_symm _ _ _ _ (multiply_associative (multiplyF C C) S gammaPairF
    (multiplyData C C x y) s AB (multiply_fast _ _ _ _ hx hy) hS hAB)
  exact cross_trans _ _ _ _ _ _ start (cross_trans _ _ _ _ _ _ exchange
    (cross_trans _ _ _ _ _ _ rebracket (cross_trans _ _ _ _ _ _ bind
      (actual_Gamma_reflection_product z R B a d (.andI hs.andE₁ hs.andE₂.andE₁)))))

def productHeight (z R B d f : PTm n) : PTm n :=
  GaussianBoundedInverseApartness.height productLinearF gammaPairF (productLinearData z R B)
    (complementaryData z R B d f) (GaussianNameBounds.U gammaPairF (complementaryData z R B d f))

theorem complementary_reciprocal (z R B a d e f : PTm n) (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input productLinearF (productHeight z R B d f) (productLinearData z R B) ⋏
      crossEquivalent (GaussianNameReciprocal.nameF productLinearF) gammaPairF
        (GaussianNameReciprocal.nameData (productHeight z R B d f) (productLinearData z R B))
        (complementaryData z R B d f) := by
  let x := productLinearData z R B
  let y := complementaryData z R B d f
  let M := GaussianNameBounds.U gammaPairF y
  have hp := hs.andE₁.andE₁
  have hx : Γ ⊢[PRAAx] pointCN productLinearF x := multiply_fast constantF S _ _ (constant_regular _)
    (GaussianSineProductName.name_regular z R B hp.andE₂.andE₁ hp.andE₂.andE₂)
  have hy : Γ ⊢[PRAAx] pointCN gammaPairF y := multiply_fast gammaF gammaF _ _
    (gamma_regular z R B a d hs.andE₁)
    (gamma_regular _ _ _ _ _ (GaussianGammaShift.shifted_source (gneg z) R B a d e f hs.andE₂))
  have hDisk : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples gammaPairF y M one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,GaussianRootApproximationWitness.pointBounds,
      M,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      GaussianNameBounds.all_samples_bounded gammaPairF y hy
  have p := cross_trans _ _ _ _ _ _ (complementary_product z R B a d e f hs)
    (GaussianBoundedInverseApartness.ones_equivalent (D z R B) x)
  exact GaussianBoundedInverseApartness.bounded_inverse_correct productLinearF gammaPairF x y M one
    (GaussianNameBounds.U_positive gammaPairF y) (le_refl one) hx hy hDisk p

theorem original_pole_free_Gamma_reflection_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        crossEquivalent (multiplyF scaledF gammaPairF) oneF
          (multiplyData scaledF gammaPairF (scaledData (var 0) (var 1) (var 2))
            (gammaPairData (var 0) (var 1) (var 2) (var 4))) (D (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (actual_Gamma_reflection_product _ _ _ _ _ Prf.hyp0))

theorem original_complementary_Gamma_reflection_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        crossEquivalent (multiplyF productLinearF gammaPairF) oneF
          (multiplyData productLinearF gammaPairF (productLinearData (var 0) (var 1) (var 2))
            (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))) (D (var 0) (var 1) (var 2))) :=
  closeUniv 7 (.impI (complementary_product _ _ _ _ _ _ _ Prf.hyp0))

theorem original_complementary_Gamma_reflection_reciprocal_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        GaussianNameReciprocal.input productLinearF
          (productHeight (var 0) (var 1) (var 2) (var 4) (var 6)) (productLinearData (var 0) (var 1) (var 2)) ⋏
        crossEquivalent (GaussianNameReciprocal.nameF productLinearF) gammaPairF
          (GaussianNameReciprocal.nameData (productHeight (var 0) (var 1) (var 2) (var 4) (var 6))
            (productLinearData (var 0) (var 1) (var 2)))
          (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))) :=
  closeUniv 7 (.impI (complementary_reciprocal _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaReflectionProduct
