import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaFixedCoefficientVariation

/-!
# A uniform ordinary coefficient mass for the original Gamma polynomials

At radius one the SAME sampled exponent has coefficient norm at most
2R+2. Its actual factorial exponential and original finite Euler head
therefore give ordinary full coefficient norm at most
2^(2R)*3^(2R+2), uniformly in precision and both finite horizons.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaUnitCoefficientMass

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaFiniteCoefficientPolynomial (polynomial totalDegree)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianRationalSyntheticBounds (natCode)
open GaussianGammaInputStaticNorm (unit_weighted_norm)
open RationalArgmin (rationalLE)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def budget (R : PTm n) : PTm n := pw two (two*R)*pw (succ two) (two*R+two)
@[simp] theorem subst_budget {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (budget R) = budget (Syn.subst σ R) := by simp [budget]

theorem exponential_norm (q R L K : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (GaussianGammaExponentCoefficientPolynomial.exponential q R L K))
      (natCode (pw (succ two) (two*R+two))) := by
  have inputUnit := unit_weighted_norm (Γ := Γ) (GaussianGammaExponentCoefficientPolynomial.polynomial q (two*R) L) (degree L)
    (GaussianGammaExponentCoefficientPolynomial.polynomial_length q (two*R) L)
    (GaussianRationalMonicReduction.added_canonical _ _ _)
  have actual := GaussianFiniteExponentialCoefficientMajorant.polynomial_numerical_majorant
    (GaussianGammaExponentCoefficientPolynomial.polynomial q (two*R) L) (degree L) K qone (two*R+two)
      (GaussianGammaExponentCoefficientPolynomial.polynomial_length q (two*R) L)
      (RationalArgmin.rationalLE_congr inputUnit.eqSymm (.eqRefl _)
        (GaussianGammaInputStaticNorm.original_input_norm q R L hR))
  exact RationalArgmin.rationalLE_congr
    (unit_weighted_norm _ _ (GaussianRationalPolynomialExponential.polynomial_length _ _ _)
      (GaussianRationalPolynomialExponential.polynomial_canonical _ _ _)) (.eqRefl _) actual

theorem original_coefficient_mass (q R L K : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial q R L K)) (natCode (budget R)) := by
  have product := GaussianRationalConvolutionNorm.product_norm (Γ := Γ)
    (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (GaussianGammaExponentCoefficientPolynomial.exponential q R L K)
    (succ (two*R)) (K*degree L) (GaussianGammaEulerHeadPolynomial.polynomial_length _)
      (GaussianGammaFiniteCoefficientPolynomial.exponential_length q R L K)
  have factors := GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _
    (GaussianCoefficientNormOrder.coefficient_numerator_nonnegative _)
    (GaussianRationalSyntheticBounds.natCode_nonnegative _)
    (GaussianGammaFixedCoefficientVariation.head_norm (Γ := Γ) R hR) (exponential_norm q R L K hR)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (GaussianRationalSyntheticBounds.natCode_multiply _ _)
    (RationalArgmin.transitive product factors)

theorem original_Gamma_unit_coefficient_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ rationalLE (coefficientNorm (polynomial (var 0) (var 1) (var 2) (var 3))) (natCode (budget (var 1)))) :=
  closeUniv 4 (.impI (original_coefficient_mass _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaUnitCoefficientMass
