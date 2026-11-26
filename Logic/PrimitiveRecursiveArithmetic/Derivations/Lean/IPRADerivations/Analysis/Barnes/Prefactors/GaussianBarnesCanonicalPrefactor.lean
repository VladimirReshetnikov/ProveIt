import IPRADerivations.Analysis.Stirling.GaussianStirlingConstant
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteApproximantName
import IPRADerivations.Analysis.Exponential.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence

/-!
# The original Barnes canonical-product prefactor

The first exponential uses the original named Stirling constant
`log(2π)/2`, multiplied by the supplied Gaussian rational `z`.
The second exponential evaluates `-(z+(1+γ)z²)/2` with the original
Euler–Mascheroni name. Both factors use a common certified exponential
radius, so the literal product also equals the exponential of their
sum at independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactor

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular gammaF gamma_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U U_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (oneF one_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalMetric (qnegative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linearF : PR 2 := multiplyF constantF GaussianStirlingConstant.nameF
def linearData (z B : PTm n) : PTm n :=
  multiplyData constantF GaussianStirlingConstant.nameF (ofGaussian z B) (GaussianStirlingConstant.nameData zero)

def quadraticCoefficientF : PR 2 := addF oneF gammaF
def quadraticCoefficientData : PTm n := addData zero zero

def quadraticF : PR 2 := multiplyF constantF quadraticCoefficientF
def quadraticData (z B : PTm n) : PTm n :=
  multiplyData constantF quadraticCoefficientF (qmul (ofGaussian z B) (ofGaussian z B)) quadraticCoefficientData

def polynomialF : PR 2 := addF constantF quadraticF
def polynomialData (z B : PTm n) : PTm n := addData (ofGaussian z B) (quadraticData z B)

def negativeHalf : PTm n := qnegative (fraction one two)
def correctionF : PR 2 := multiplyF constantF polynomialF
def correctionData (z B : PTm n) : PTm n := multiplyData constantF polynomialF negativeHalf (polynomialData z B)

def radius (z B : PTm n) : PTm n := U linearF (linearData z B)+U correctionF (correctionData z B)

def nameF : PR 2 := GaussianExponentialAddition.productF linearF correctionF
def data (z B : PTm n) : PTm n :=
  GaussianExponentialAddition.productData linearF correctionF (radius z B) (linearData z B) (correctionData z B)

def combinedF : PR 2 := GaussianExponentialAddition.sumF linearF correctionF
def combinedData (z B : PTm n) : PTm n :=
  GaussianExponentialAddition.sumData (radius z B) (linearData z B) (correctionData z B)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (data z B) = data (Syn.subst σ z) (Syn.subst σ B) := by
  simp [data,radius,linearData,correctionData,polynomialData,quadraticData,quadraticCoefficientData,negativeHalf,
    one,two]

@[simp] theorem subst_combinedData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (combinedData z B) = combinedData (Syn.subst σ z) (Syn.subst σ B) := by
  simp [combinedData,radius,linearData,correctionData,polynomialData,quadraticData,quadraticCoefficientData,
    negativeHalf,one,two]

theorem linear_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN linearF (linearData z B) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianStirlingConstant.name_regular zero)

theorem quadratic_coefficient_regular : Γ ⊢[PRAAx] pointCN quadraticCoefficientF (quadraticCoefficientData : PTm n) :=
  add_fast _ _ _ _ (one_fast zero) gamma_regular

theorem correction_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN correctionF (correctionData z B) := by
  have quadratic := multiply_fast constantF quadraticCoefficientF (qmul (ofGaussian z B) (ofGaussian z B))
    quadraticCoefficientData (constant_regular (Γ := Γ) _) quadratic_coefficient_regular
  have polynomial := add_fast constantF quadraticF (ofGaussian z B) (quadraticData z B) (constant_regular _) quadratic
  exact multiply_fast _ _ _ _ (constant_regular _) polynomial

theorem radius_positive (z B : PTm n) : Γ ⊢[PRAAx] le one (radius z B) :=
  le_trans (U_positive linearF (linearData z B)) (le_add_right _ _)

theorem linear_input (z B : PTm n) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input linearF (radius z B) (linearData z B) :=
  GaussianExponentialRadiusIndependence.input_widen _ _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (linear_regular z B)) (le_add_right _ _)

theorem correction_input (z B : PTm n) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input correctionF (radius z B) (correctionData z B) :=
  GaussianExponentialRadiusIndependence.input_widen _ _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (correction_regular z B)) (le_add_left _ _)

theorem regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data z B) :=
  multiply_fast _ _ _ _
    (GaussianRadiusExponentialName.name_regular _ _ _ (linear_input z B))
    (GaussianRadiusExponentialName.name_regular _ _ _ (correction_input z B))

theorem combined (z B : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF combinedF (data z B) (combinedData z B) :=
  GaussianExponentialAddition.exponential_add_cross _ _ _ _ _ (radius_positive z B)
    (linear_input z B) (correction_input z B)

theorem actual_Barnes_canonical_prefactor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN nameF (data (var 0) (var 1)) ⋏
      crossEquivalent nameF combinedF (data (var 0) (var 1)) (combinedData (var 0) (var 1))) :=
  closeUniv 2 (.andI (regular _ _) (combined _ _))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactor
