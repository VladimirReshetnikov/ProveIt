import IPRADerivations.Analysis.GaussianGaussDuplicationFactor
import IPRADerivations.Analysis.GaussianGaussEulerFiniteIdentity
import IPRADerivations.Analysis.GaussianGaussExplicitShiftedProducts

/-!
# The original Gamma duplication identity

The two original shifted Gamma names at the shared denominator
agree with the original power of two, the bounded square-root name
for pi, and the original Gamma name at twice the argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussDuplication

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGaussEulerFiniteIdentity (cleared_Gauss_multiplication)
open GaussianGaussExplicitShiftedProducts (twoRowsF twoRowsData two_factors)
open GaussianGaussMultiplicationCofinalProducts (leftF leftData rightF rightData innerF innerData referenceF referenceData)
open GaussianGaussMultiplicationCofinalRows (limit_power_regular scaled_regular scaledData)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "SqrtPi" => GaussianGammaHalfSqrtPi.nameF

abbrev coefficientF : PR 2 := multiplyF powerF SqrtPi
abbrev duplicationF : PR 2 := multiplyF coefficientF gammaF
def coefficientData (z R B x : PTm n) : PTm n :=
  multiplyData powerF SqrtPi (limitData z R B two) x
def duplicationData (z R B d x : PTm n) : PTm n :=
  multiplyData coefficientF gammaF (coefficientData z R B x) (scaledData z R B two d)

theorem duplication_right (z R B a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B two a d) :
    Γ ⊢[PRAAx] crossEquivalent rightF duplicationF (rightData z R B two d) (duplicationData z R B d x) := by
  let P := limitData z R B two
  let G := scaledData z R B two d
  let C := referenceData (two : PTm n)
  have hP := limit_power_regular z R B two a d hs
  have hG := scaled_regular z R B two a d hs
  have hC := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) (two : PTm n)
  have s := GaussianGaussDuplicationFactor.reference_sqrt_pi (Γ := Γ) x
  have hX := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ s) s
  have hI := multiply_fast powerF gammaF P G hP hG
  have replacement := multiply_cross innerF innerF referenceF SqrtPi (innerData z R B two d)
    (innerData z R B two d) C x hI hI hC hX (cross_refl _ _ hI) s
  have swapped := multiply_cross powerF powerF (multiplyF gammaF SqrtPi) (multiplyF SqrtPi gammaF)
    P P (multiplyData gammaF SqrtPi G x) (multiplyData SqrtPi gammaF x G)
    hP hP (multiply_fast _ _ _ _ hG hX) (multiply_fast _ _ _ _ hX hG)
    (cross_refl _ _ hP) (multiply_commutative gammaF SqrtPi G x hG hX)
  exact cross_trans _ _ _ _ _ _ replacement (cross_trans _ _ _ _ _ _
    (multiply_associative powerF gammaF SqrtPi P G x hP hG hX)
    (cross_trans _ _ _ _ _ _ swapped (cross_symm _ _ _ _ (multiply_associative powerF SqrtPi gammaF P x G hP hX hG))))

theorem duplication (z R B a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B two a d) :
    Γ ⊢[PRAAx] crossEquivalent twoRowsF duplicationF (twoRowsData z R B two d) (duplicationData z R B d x) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (two_factors z R B a d hs))
    (cross_trans _ _ _ _ _ _ (cleared_Gauss_multiplication z R B two a d hs) (duplication_right z R B a d x hs))

theorem actual_Gauss_duplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) two (var 3) (var 4) ⟶
      crossEquivalent twoRowsF duplicationF (twoRowsData (var 0) (var 1) (var 2) two (var 4))
        (duplicationData (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.impI (duplication _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussDuplication
