import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaReflectionProduct
import IPRADerivations.Analysis.Trigonometry.GaussianNamedSineSincFactorization
import IPRADerivations.Analysis.Gamma.GaussianGammaHalfPiName

/-!
# Transfer of the complementary reflection product to the original sine

An instance of the literal sine product identification at the original
named argument π(z/B) implies the cleared reflection identity of the
original Gamma and sine names. The existing product theorem supplies
the two Gamma factors and their complement shift.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaReflectionSineTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaReflectionProduct
  (complementarySource complementaryData gammaPairF productLinearF productLinearData complementary_product)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNamedSineTaylor (imaginaryF imaginary_input)
open GaussianNamedSineFromExponential (sineF sineData sine_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)
open GaussianRationalHorner (ofGaussian)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "S" => GaussianSineProductName.nameF

def argumentF : PR 2 := multiplyF P constantF
def argumentData (z B x : PTm n) : PTm n := multiplyData P constantF x (ofGaussian z B)
def argumentRadius (z B x : PTm n) : PTm n := GaussianNameBounds.U argumentF (argumentData z B x)
def sineAtPiF : PR 2 := sineF (imaginaryF argumentF)
def sineAtPiData (z B x : PTm n) : PTm n :=
  sineData (imaginaryF argumentF) (argumentRadius z B x) (argumentData z B x)
def productIdentification (z R B x : PTm n) : Fm PTm n :=
  crossEquivalent S (GaussianNamedSinc.nameF argumentF) (GaussianSineProductName.data z R B)
    (GaussianNamedSinc.data argumentF (argumentRadius z B x) (argumentData z B x))

theorem sine_as_product (z R B x : PTm n) (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (h : Γ ⊢[PRAAx] productIdentification z R B x) :
    Γ ⊢[PRAAx] crossEquivalent sineAtPiF (multiplyF P productLinearF)
      (sineAtPiData z B x) (multiplyData P productLinearF x (productLinearData z R B)) := by
  let C := constantF
  let Z := ofGaussian z B
  let X := argumentData z B x
  let U := argumentRadius z B x
  let Y := GaussianNamedSinc.data argumentF U X
  let Q := GaussianSineProductName.data z R B
  let T := GaussianNamedSinc.nameF argumentF
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hz := constant_regular (Γ := Γ) Z
  have ha := multiply_fast P C x Z hp hz
  have input := GaussianGammaFiniteApproximantName.exponential_input argumentF X ha
  have sinc := GaussianNamedSinc.name_regular argumentF U X input
  have sine := GaussianNamedSineSincFactorization.original_sine_factors argumentF U X input
  have prod := GaussianSineProductName.name_regular z R B hs.andE₂.andE₁ hs.andE₂.andE₂
  have replaced := multiply_cross argumentF argumentF T S X X Y Q ha ha sinc prod (cross_refl _ _ ha)
    (cross_symm _ _ _ _ h)
  exact cross_trans _ _ _ _ _ _ sine
    (cross_trans _ _ _ _ _ _ replaced (multiply_associative P C S x Z Q hp hz prod))

theorem cleared_reflection (z R B a d e f x : PTm n) (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f)
    (h : Γ ⊢[PRAAx] productIdentification z R B x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF sineAtPiF gammaPairF) P
      (multiplyData sineAtPiF gammaPairF (sineAtPiData z B x) (complementaryData z R B d f)) x := by
  let C := constantF
  let G := gammaPairF
  let X := argumentData z B x
  let Y := complementaryData z R B d f
  let Z := productLinearData z R B
  let L := productLinearF
  have p := hs.andE₁.andE₁
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hZ := multiply_fast C S (ofGaussian z B) (GaussianSineProductName.data z R B) (constant_regular _)
    (GaussianSineProductName.name_regular z R B p.andE₂.andE₁ p.andE₂.andE₂)
  have hG := multiply_fast _ _ _ _ (GaussianGammaReciprocalInverse.gamma_regular z R B a d hs.andE₁)
    (GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _
      (GaussianGammaShift.shifted_source _ R B a d e f hs.andE₂))
  have arg := multiply_fast P C x (ofGaussian z B) hp (constant_regular _)
  have hi := GaussianGammaFiniteApproximantName.exponential_input argumentF X arg
  have hsi := sine_regular (imaginaryF argumentF) (argumentRadius z B x) X (imaginary_input _ _ _ hi)
  have replace := multiply_cross sineAtPiF (multiplyF P L) G G (sineAtPiData z B x)
    (multiplyData P L x Z) Y Y hsi (multiply_fast P L x Z hp hZ) hG hG
    (sine_as_product z R B x p h) (cross_refl _ _ hG)
  have assoc := multiply_associative P L G x Z Y hp hZ hG
  have factor := cross_trans _ _ _ _ _ _ (complementary_product z R B a d e f hs)
    (GaussianBoundedInverseApartness.ones_equivalent (GaussianGammaC7Name.data z R B) x)
  have unit := multiply_cross P P (multiplyF L G) oneF x x (multiplyData L G Z Y) x hp hp
    (multiply_fast L G Z Y hZ hG) (one_fast x) (cross_refl _ _ hp) factor
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ unit (multiply_one P x hp)))

theorem original_cleared_Gamma_sine_reflection_of_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        productIdentification (var 0) (var 1) (var 2) (var 7) ⟶
        crossEquivalent (multiplyF sineAtPiF gammaPairF) P
          (multiplyData sineAtPiF gammaPairF (sineAtPiData (var 0) (var 2) (var 7))
            (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))) (var 7)) :=
  closeUniv 8 (.impI (.impI (cleared_reflection _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaReflectionSineTransfer
