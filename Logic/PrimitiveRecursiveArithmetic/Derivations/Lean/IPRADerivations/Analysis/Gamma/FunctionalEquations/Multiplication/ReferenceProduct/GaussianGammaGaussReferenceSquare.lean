import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferenceSquareAlgebra
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionPowerConstant
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamilyAlgebra

/-!
# Closed squared Gauss reference normalization

The actual finite products of the cleared reflection rows split into
the independently normalized sine and Gamma factors. The M1 value
removes the sine factors. The target is the actual finite family
power of the original doubled π name, multiplied by `1/(N+1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceSquare

open_ipra
open GaussianCyclicSineProductSquare (data)
open GaussianGammaGaussReflectionFamily (reflection_body_eq sineBody pairBody leftBody rightBody piBody
  sine_rows left_rows right_rows pi_rows)
open GaussianGammaGaussReferenceSquareAlgebra (reflectionF reflectionData leftF rightF leftData rightData
  pairF pairData piPowerF piPowerData pi_power_regular referenceSquareF referenceSquareData targetF targetData
  reflectionFactorization squared_normalization)
open GaussianGammaGaussReflectionPowerConstant (twoBody twoPowerF twoPowerData reciprocalModulus
  two_rows two_power_cross power_times_reciprocal)
open GaussianGammaGaussReflectionCancellation (inverseRatio)
open GaussianGammaReflectionProduct (gammaPairF)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedFiniteProductFamily (productData family_product_regular)
open GaussianNamedFiniteProductFamilyAlgebra (multiplyBody multiply_regular family_multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (multiply_associative)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF
local notation "S" => GaussianNamedSineFromExponential.sineF GaussianCyclicExponentialRoots.angleF
local notation "FSin" => GaussianGammaGaussReflectionSineProduct.nameF
local notation "FRow" => GaussianNamedFiniteProductFamily.rowF
local notation "FProd" => GaussianNamedFiniteProductName.nameF

theorem factorization (N x : PTm n) : Γ ⊢[PRAAx] reflectionFactorization N x := by
  let X := data N x
  let T := FProd (FRow gammaPairF pairBody)
  let Y := productData gammaPairF pairBody N X
  let Z := GaussianGammaGaussReflectionSineProduct.nameData N x
  have hL := left_rows (Γ := Γ) N x
  have hR := right_rows (Γ := Γ) N x
  have hS := sine_rows (Γ := Γ) N x
  have hT := multiply_regular gammaF gammaF leftBody rightBody N X hL hR
  have split := family_multiply_cross S gammaPairF sineBody pairBody N X hS hT
  have first : Γ ⊢[PRAAx] crossEquivalent reflectionF (multiplyF FSin T) (reflectionData N x)
      (multiplyData FSin T Z Y) := by
    simpa only [reflectionF, reflectionData, reflection_body_eq, multiplyBody,
      GaussianGammaGaussReflectionRow.rowF, GaussianGammaGaussReflectionSineProduct.nameF,
      GaussianGammaGaussReflectionSineProduct.familyRowF, GaussianGammaGaussReflectionSineProduct.nameData,
      X, T, Y, Z] using split
  have pairSplit : Γ ⊢[PRAAx] crossEquivalent T pairF Y (pairData N x) :=
    family_multiply_cross gammaF gammaF leftBody rightBody N X hL hR
  have hF := GaussianGammaGaussReflectionSineProduct.name_regular (Γ := Γ) N x
  have ht := family_product_regular _ _ _ _ hT
  have hp := multiply_fast leftF rightF _ _ (GaussianGammaGaussReferenceSquareAlgebra.left_regular (Γ := Γ) N x)
    (GaussianGammaGaussReferenceSquareAlgebra.right_regular N x)
  exact cross_trans _ _ _ _ _ _ first
    (multiply_cross FSin FSin T pairF Z Z Y (pairData N x) hF hF ht hp (cross_refl _ _ hF) pairSplit)

def doubledPiBody : PTm 2 := multiplyBody P C piBody twoBody
def doubledPiPowerF : PR 2 := FProd (FRow (multiplyF P C) doubledPiBody)
def doubledPiPowerData (N x : PTm n) : PTm n := productData (multiplyF P C) doubledPiBody N (data N x)
def normalizationF : PR 2 := multiplyF doubledPiPowerF C
def normalizationData (N x : PTm n) : PTm n :=
  multiplyData doubledPiPowerF C (doubledPiPowerData N x) (reciprocalModulus N)

theorem target_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent normalizationF targetF (normalizationData N x) (targetData N x) := by
  let X := data N x
  let Y := doubledPiPowerData N x
  let U := piPowerData N x
  let V := twoPowerData N X
  let B := naturalPoint (unit N)
  let D := reciprocalModulus N
  have pi := pi_rows (Γ := Γ) N x
  have tw := two_rows (Γ := Γ) N X
  have hPi := pi_power_regular (Γ := Γ) N x
  have hB := constant_regular (Γ := Γ) B
  have hD := constant_regular (Γ := Γ) D
  have hPow : Γ ⊢[PRAAx] pointCN doubledPiPowerF Y :=
    family_product_regular _ _ _ _ (multiply_regular P C piBody twoBody N X pi tw)
  have split : Γ ⊢[PRAAx] crossEquivalent doubledPiPowerF (multiplyF piPowerF twoPowerF) Y
      (multiplyData piPowerF twoPowerF U V) :=
    family_multiply_cross P C piBody twoBody N X pi tw
  have splitConst := multiply_cross piPowerF piPowerF twoPowerF C U U V B hPi hPi
    (family_product_regular C twoBody N X tw) hB
    (cross_refl _ _ hPi) (two_power_cross N X)
  have first := multiply_cross doubledPiPowerF (multiplyF piPowerF C) C C Y
    (multiplyData piPowerF C U B) D D hPow (multiply_fast _ _ _ _ hPi hB) hD hD
    (cross_trans _ _ _ _ _ _ split splitConst) (cross_refl _ _ hD)
  have product : Γ ⊢[PRAAx] crossEquivalent (multiplyF C C) C (multiplyData C C B D) (inverseRatio N) :=
    cross_trans _ _ _ _ _ _ (constant_product_cross B D)
    (constant_data_cross _ _ (power_times_reciprocal N))
  have last := multiply_cross piPowerF piPowerF (multiplyF C C) C U U (multiplyData C C B D) (inverseRatio N)
    hPi hPi (multiply_fast _ _ _ _ hB hD) (constant_regular _) (cross_refl _ _ hPi) product
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (multiply_associative piPowerF C C U B D hPi hB hD) last)

theorem actual_square_normalization (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent referenceSquareF normalizationF (referenceSquareData N) (normalizationData N x) :=
  cross_trans _ _ _ _ _ _ (squared_normalization N x (factorization N x)) (cross_symm _ _ _ _ (target_cross N x))

theorem actual_Gauss_squared_reference_normalization_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent referenceSquareF normalizationF (referenceSquareData (var 1)) (normalizationData (var 1) (var 0))) :=
  closeUniv 2 (actual_square_normalization _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceSquare
