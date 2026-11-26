import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionSineProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionReferenceProducts
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionCancellation

/-!
# Squared reference normalization from the finite family factorization

The product of the literal cleared reflection rows factors into the
M1 sine product and the two reference products. Both reference orders
name the existing original Gauss reference product. Canceling the
literal M1 ratio gives the squared normalization as the product of
`N` copies of π times the literal rational `2^N/(N+1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceSquareAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicSineProductSquare (data)
open GaussianCyclicSineProductRatio (ratio)
open GaussianGammaGaussReflectionRow (rowF)
open GaussianGammaGaussReflectionFamily (leftBody rightBody reflectionBody piBody products_cross left_rows right_rows pi_rows)
open GaussianGammaGaussReflectionSineProduct (normalized_sine_product)
open GaussianGammaGaussReflectionReferenceProducts (left_reference_product right_reference_product)
open GaussianGammaGaussReflectionCancellation (inverseRatio cancel_sine_ratio)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedFiniteProductFamily (productData family_product_regular)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF
local notation "G" => GaussianGammaGaussReferenceProduct.nameF
local notation "S" => GaussianGammaGaussReflectionSineProduct.nameF
local notation "FRow" => GaussianNamedFiniteProductFamily.rowF
local notation "FProd" => GaussianNamedFiniteProductName.nameF

def reflectionF : PR 2 := FProd (FRow rowF reflectionBody)
def reflectionData (N x : PTm n) : PTm n := productData rowF reflectionBody N (data N x)
def leftF : PR 2 := FProd (FRow gammaF leftBody)
def rightF : PR 2 := FProd (FRow gammaF rightBody)
def leftData (N x : PTm n) : PTm n := productData gammaF leftBody N (data N x)
def rightData (N x : PTm n) : PTm n := productData gammaF rightBody N (data N x)
def pairF : PR 2 := multiplyF leftF rightF
def pairData (N x : PTm n) : PTm n := multiplyData leftF rightF (leftData N x) (rightData N x)
def piPowerF : PR 2 := FProd (FRow P piBody)
def piPowerData (N x : PTm n) : PTm n := productData P piBody N (data N x)
def referenceSquareF : PR 2 := multiplyF G G
def referenceSquareData (N : PTm n) : PTm n :=
  multiplyData G G (GaussianGammaGaussReferenceProduct.data (succ N)) (GaussianGammaGaussReferenceProduct.data (succ N))
def targetF : PR 2 := multiplyF piPowerF C
def targetData (N x : PTm n) : PTm n := multiplyData piPowerF C (piPowerData N x) (inverseRatio N)

/-- This is the sole finite-family factorization input to the reference normalization. -/
def reflectionFactorization (N x : PTm n) : Fm PTm n :=
  crossEquivalent reflectionF (multiplyF S pairF) (reflectionData N x)
    (multiplyData S pairF (GaussianGammaGaussReflectionSineProduct.nameData N x) (pairData N x))

theorem left_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN leftF (leftData N x) :=
  family_product_regular _ _ _ _ (left_rows N x)
theorem right_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN rightF (rightData N x) :=
  family_product_regular _ _ _ _ (right_rows N x)
theorem pi_power_regular (N x : PTm n) : Γ ⊢[PRAAx] pointCN piPowerF (piPowerData N x) :=
  family_product_regular _ _ _ _ (pi_rows N x)

theorem reference_square_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN referenceSquareF (referenceSquareData N) :=
  multiply_fast G G _ _ (GaussianGammaGaussReferenceProduct.name_regular (succ N))
    (GaussianGammaGaussReferenceProduct.name_regular (succ N))

theorem gamma_factor_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent pairF referenceSquareF (pairData N x) (referenceSquareData N) := by
  have h := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) (succ N)
  exact multiply_cross leftF G rightF G (leftData N x) _ (rightData N x) _
    (left_regular N x) h (right_regular N x) h (left_reference_product N x) (right_reference_product N x)

theorem squared_cleared (N x : PTm n) (h : Γ ⊢[PRAAx] reflectionFactorization N x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF referenceSquareF C) piPowerF
      (multiplyData referenceSquareF C (referenceSquareData N) (ratio N)) (piPowerData N x) := by
  let z := GaussianGammaGaussReflectionSineProduct.nameData N x
  let a := pairData N x
  let b := referenceSquareData N
  let d := ratio N
  have hR := reference_square_regular (Γ := Γ) N
  have hC := constant_regular (Γ := Γ) d
  have hPair := multiply_fast leftF rightF (leftData N x) (rightData N x) (left_regular (Γ := Γ) N x) (right_regular N x)
  have lift := multiply_cross S C pairF referenceSquareF z d a b
    (GaussianGammaGaussReflectionSineProduct.name_regular N x) hC hPair hR
    (normalized_sine_product N x) (gamma_factor_cross N x)
  have original : Γ ⊢[PRAAx] crossEquivalent reflectionF piPowerF (reflectionData N x) (piPowerData N x) :=
    products_cross N x
  have fromOriginal : Γ ⊢[PRAAx] crossEquivalent (multiplyF S pairF) piPowerF (multiplyData S pairF z a) (piPowerData N x) :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ h) original
  exact cross_trans _ _ _ _ _ _ (multiply_commutative referenceSquareF C b d hR hC)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ lift) fromOriginal)

theorem squared_normalization (N x : PTm n) (h : Γ ⊢[PRAAx] reflectionFactorization N x) :
    Γ ⊢[PRAAx] crossEquivalent referenceSquareF targetF (referenceSquareData N) (targetData N x) :=
  cancel_sine_ratio referenceSquareF piPowerF N _ _ (reference_square_regular N) (pi_power_regular N x)
    (squared_cleared N x h)

theorem actual_Gauss_reference_square_of_factorization_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (reflectionFactorization (var 1) (var 0) ⟶
        crossEquivalent referenceSquareF targetF (referenceSquareData (var 1)) (targetData (var 1) (var 0))) :=
  closeUniv 2 (.impI (squared_normalization _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceSquareAlgebra
