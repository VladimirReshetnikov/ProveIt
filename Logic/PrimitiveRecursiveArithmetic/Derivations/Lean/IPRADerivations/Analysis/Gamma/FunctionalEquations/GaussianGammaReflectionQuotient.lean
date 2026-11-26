import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaReflectionSineTransfer
import IPRADerivations.Analysis.Trigonometry.GaussianSineReflectionLower

/-!
# The quotient form of the original Gamma reflection identity

Multiplication of the cleared identity by the certified reciprocal
of the original sine gives the ordinary reflection quotient. The
reciprocal is read from the actual sine program and its apartness
certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 245000

namespace LeanProofs.IPRA.Analysis.GaussianGammaReflectionQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaReflectionProduct (complementarySource complementaryData gammaPairF)
open GaussianGammaReflectionSineTransfer (argumentF argumentData argumentRadius sineAtPiF sineAtPiData productIdentification)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameReciprocal (anchor apart nameData name_fast product_one)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative multiply_one)
open GaussianRationalHorner (ofGaussian)
open GaussianSineProductReflectionLower (numerator denominator numerator_positive denominator_positive)
open GaussianSineReflectionLower (actual_sine_lower threshold)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF

theorem divide_cleared (F G H : PR 2) (x y z a : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN H z)
    (ha : Γ ⊢[PRAAx] apart F a x)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF F G) H (multiplyData F G x y) z) :
    Γ ⊢[PRAAx] crossEquivalent G (multiplyF H (GaussianNameReciprocal.nameF F)) y
      (multiplyData H (GaussianNameReciprocal.nameF F) z (nameData a x)) := by
  let I := GaussianNameReciprocal.nameF F
  let X := nameData a x
  let Y := multiplyData G F y x
  let Z := multiplyData F I x X
  have hi := name_fast F a x hf ha
  have hGF := multiply_fast G F y x hg hf
  have hFI := multiply_fast F I x X hf hi
  have e := cross_trans _ _ _ _ _ _ (multiply_commutative G F y x hg hf) he
  have quo := multiply_cross (multiplyF G F) H I I Y z X X hGF hh hi hi e (cross_refl _ _ hi)
  have prod := cross_trans _ _ _ _ _ _ (product_one F a x hf ha)
    (GaussianBoundedInverseApartness.ones_equivalent x y)
  have unit := multiply_cross G G (multiplyF F I) oneF y y Z y hg hg hFI (one_fast y)
    (cross_refl _ _ hg) prod
  have cancel := cross_trans _ _ _ _ _ _ (multiply_associative G F I y x X hg hf hi)
    (cross_trans _ _ _ _ _ _ unit (multiply_one G y hg))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ cancel) quo

def quotientF : PR 2 := multiplyF P (GaussianNameReciprocal.nameF sineAtPiF)
def quotientData (z B x h : PTm n) : PTm n :=
  multiplyData P (GaussianNameReciprocal.nameF sineAtPiF) x (nameData h (sineAtPiData z B x))

theorem quotient_of_cleared (z R B a d e f x h : PTm n)
    (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f)
    (ha : Γ ⊢[PRAAx] apart sineAtPiF h (sineAtPiData z B x))
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF sineAtPiF gammaPairF) P
      (multiplyData sineAtPiF gammaPairF (sineAtPiData z B x) (complementaryData z R B d f)) x) :
    Γ ⊢[PRAAx] crossEquivalent gammaPairF quotientF (complementaryData z R B d f) (quotientData z B x h) := by
  let u := argumentData z B x
  let U := argumentRadius z B x
  have hP := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hC := GaussianGammaCanonicalExponent.constant_regular (Γ := Γ) (ofGaussian z B)
  have harg := multiply_fast P GaussianGammaCanonicalExponent.constantF x (ofGaussian z B) hP hC
  have hin := GaussianGammaFiniteApproximantName.exponential_input argumentF u harg
  have hS := GaussianNamedSineFromExponential.sine_regular _ U u (GaussianNamedSineTaylor.imaginary_input _ _ _ hin)
  have hG : Γ ⊢[PRAAx] pointCN gammaPairF (complementaryData z R B d f) :=
    multiply_fast _ _ _ _ (GaussianGammaReciprocalInverse.gamma_regular z R B a d hs.andE₁)
      (GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _
        (GaussianGammaShift.shifted_source _ R B a d e f hs.andE₂))
  exact divide_cleared sineAtPiF gammaPairF P (sineAtPiData z B x) (complementaryData z R B d f) x h hS hG hP ha he

def reciprocalHeight (d R L : PTm n) : PTm n := GaussianFastValueCut.normalizer (threshold d R L)

theorem apart_of_product (z R B a d L x : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianSineProductReflectionLower.source z R B a d L)
    (hT7 : Γ ⊢[PRAAx] productIdentification z R B x) :
    Γ ⊢[PRAAx] apart sineAtPiF (reciprocalHeight d R L) (sineAtPiData z B x) := by
  let D := denominator d R L
  let A := numerator a L
  let H := reciprocalHeight d R L
  let p := anchor H
  let q := ap2 sineAtPiF p (sineAtPiData z B x)
  have hD : Γ ⊢[PRAAx] le one D := denominator_positive d R L (le_trans hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂)
  have hA : Γ ⊢[PRAAx] le one A := numerator_positive a L hs.andE₁.andE₂.andE₁
  have hBudget : Γ ⊢[PRAAx] le (threshold d R L) (unit H) := GaussianFastValueCut.normalizer_budget _
  have hw : Γ ⊢[PRAAx] le (threshold d R L) (unit p) :=
    le_trans hBudget (GaussianExponentialReference.unit_monotone (le_add_right H two))
  have hDen : Γ ⊢[PRAAx] le D (threshold d R L) := le_of_eq_add (d := L+D) (by
    unfold threshold
    change Γ ⊢[PRAAx] L+two*D ≐ D+(L+D)
    ipra_ring)
  have hl := actual_sine_lower z R B a d L p x hs hT7 hw
  exact GaussianRationalLowerBounds.name_lower q A (unit H) hA (unit_positive H)
    (GaussianBoundedInverseApartness.weaken_denominator q A D (unit H) hD (le_trans hDen hBudget) hl)

theorem quotient_of_product (z R B a d e f L x : PTm n)
    (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f)
    (hR3 : Γ ⊢[PRAAx] GaussianSineProductReflectionLower.source z R B a d L)
    (hT7 : Γ ⊢[PRAAx] productIdentification z R B x) :
    Γ ⊢[PRAAx] crossEquivalent gammaPairF quotientF (complementaryData z R B d f)
      (quotientData z B x (reciprocalHeight d R L)) :=
  quotient_of_cleared z R B a d e f x (reciprocalHeight d R L) hs (apart_of_product z R B a d L x hR3 hT7)
    (GaussianGammaReflectionSineTransfer.cleared_reflection z R B a d e f x hs hT7)

theorem actual_Gamma_reflection_quotient_of_cleared_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        apart sineAtPiF (var 8) (sineAtPiData (var 0) (var 2) (var 7)) ⟶
        crossEquivalent (multiplyF sineAtPiF gammaPairF) P
          (multiplyData sineAtPiF gammaPairF (sineAtPiData (var 0) (var 2) (var 7))
            (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))) (var 7) ⟶
        crossEquivalent gammaPairF quotientF (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))
          (quotientData (var 0) (var 2) (var 7) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (quotient_of_cleared _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaReflectionQuotient
