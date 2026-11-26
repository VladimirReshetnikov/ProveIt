import IPRADerivations.Analysis.Polynomials.GaussianPolynomialProductLeftPadding
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaFiniteCoefficientStability

/-!
# Original Gamma coefficient stabilization at every degree

Zero padding raises the actual finite head degree without changing any
original coefficient or evaluation. Existing guarded low-Cauchy proofs
can therefore be applied at every requested exponent. The resulting
equalities are on the SAME original unpadded polynomial and cofinal
observation programs, without the former e<=2R+1 restriction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaAllDegreeCoefficientStability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaFiniteCoefficientPolynomial (polynomial totalDegree)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient cofinalObservation)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianPolynomialLowJetProduct (jetEqual)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def paddedHead (R e : PTm n) : PTm n := leftPad (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) e
def headDegree (R e : PTm n) : PTm n := e+succ (two*R)
def exponential (q R L K : PTm n) : PTm n := GaussianGammaExponentCoefficientPolynomial.exponential q R L K
def paddedPolynomial (q R L K e : PTm n) : PTm n := product (paddedHead R e) (exponential q R L K) (headDegree R e) (K*degree L)
@[simp] theorem subst_paddedHead {m : ℕ} (σ : Fin n → PTm m) (R e : PTm n) :
    Syn.subst σ (paddedHead R e) = paddedHead (Syn.subst σ R) (Syn.subst σ e) := by simp [paddedHead]
@[simp] theorem subst_headDegree {m : ℕ} (σ : Fin n → PTm m) (R e : PTm n) :
    Syn.subst σ (headDegree R e) = headDegree (Syn.subst σ R) (Syn.subst σ e) := by simp [headDegree]
@[simp] theorem subst_exponential {m : ℕ} (σ : Fin n → PTm m) (q R L K : PTm n) :
    Syn.subst σ (exponential q R L K) = exponential (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ K) := by simp [exponential]
@[simp] theorem subst_paddedPolynomial {m : ℕ} (σ : Fin n → PTm m) (q R L K e : PTm n) :
    Syn.subst σ (paddedPolynomial q R L K e) = paddedPolynomial (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ e) := by simp [paddedPolynomial]

theorem padding_reader (q R L K e : PTm n) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (paddedPolynomial q R L K e) (headDegree R e+K*degree L) e ≐
      exponentCoefficient (polynomial q R L K) (totalDegree R L K) e := by
  have bound := GaussianGammaFiniteCoefficientStability.output_degree_bound (Γ := Γ) e K L hK
  exact GaussianPolynomialProductLeftPadding.original_reader _ _ _ _ _ _
    (GaussianGammaEulerHeadPolynomial.polynomial_length (two*R)) (GaussianRationalPolynomialExponential.stage_length _ _ _ _)
    (le_trans bound (le_add_left _ _))

theorem whole_horizon_reader (q R L M K T e : PTm n)
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hM : Γ ⊢[PRAAx] le e (degree M))
    (hK : Γ ⊢[PRAAx] le e K) (hT : Γ ⊢[PRAAx] le e T) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q R L K) (totalDegree R L K) e ≐
      exponentCoefficient (polynomial q R M T) (totalDegree R M T) e := by
  have head : Γ ⊢[PRAAx] jetEqual (paddedHead R e) (headDegree R e) (paddedHead R e) (headDegree R e) e := .allI (.impI (.eqRefl _))
  have comparison := GaussianPolynomialLowJetProduct.product_reader (Γ := Γ) _ _ _ _ _ _ _ _ _ _ head
    (GaussianGammaFiniteCoefficientStability.exponential_jet q (two*R) L M K T e hL hM hK hT) (le_refl e)
    (le_add_right e _) (GaussianGammaFiniteCoefficientStability.output_degree_bound e K L hK)
    (le_add_right e _) (GaussianGammaFiniteCoefficientStability.output_degree_bound e T M hT)
  exact (padding_reader q R L K e hK).eqSymm.eqTrans (comparison.eqTrans (padding_reader q R M T e hT))

theorem original_fixed_horizon (q R L K e : PTm n)
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q R L K) (totalDegree R L K) e ≐ fixedCoefficient q R e :=
  whole_horizon_reader q R L e K e e hL (le_of_eq_add (d := two) (by unfold degree; ipra_ring)) hK (le_refl e)

theorem cofinal_observation_fixed (p R e : PTm n) : Γ ⊢[PRAAx]
    cofinalObservation p R e ≐ fixedCoefficient (GaussianGammaCofinalCoefficientName.coefficientPrecision (p+e) R) R e := by
  have horizon := le_trans (le_add_left e p) (GaussianGammaCofinalCoefficientName.degree_cutoff_cofinal (Γ := Γ) (p+e) R)
  exact original_fixed_horizon _ _ _ _ _
    (le_trans horizon (le_of_eq_add (d := two) (by unfold degree; ipra_ring)))
    (le_trans (le_add_left e p) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (p+e) R))

theorem original_all_degree_Gamma_finite_coefficient_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (degree (var 2)) ⟶ le (var 4) (var 3) ⟶
      exponentCoefficient (polynomial (var 0) (var 1) (var 2) (var 3)) (totalDegree (var 1) (var 2) (var 3)) (var 4) ≐
        fixedCoefficient (var 0) (var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (original_fixed_horizon _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_all_degree_Gamma_cofinal_fixed_expression_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cofinalObservation (var 0) (var 1) (var 2) ≐
      fixedCoefficient (GaussianGammaCofinalCoefficientName.coefficientPrecision (var 0+var 2) (var 1)) (var 1) (var 2)) :=
  closeUniv 3 (cofinal_observation_fixed _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaAllDegreeCoefficientStability
