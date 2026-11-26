import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialExponentAlgebra

/-!
# The actual finite product Euler kernel is the sum of its actual kernels

For separately proved original low jets Euler(P)=A*P and Euler(Q)=B*Q,
the actual finite product has Euler(P*Q)=(A+B)*(P*Q) through the stated
degree bounds. Genuine original product Leibniz, low-jet convolution
congruence, association, commutation and coefficient distribution derive
the result. Shapes and the two component jets are explicit supplier
inputs; the resulting product identity is never an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialProductEulerFactorization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialProduct (product product_length)
open GaussianRationalPolynomialBuffers (added)
open GaussianRationalEulerCoefficients (euler leibniz)
open GaussianPolynomialLowJetProduct (jetEqual product_reader)
open GaussianFiniteLogarithmCoefficientRecursion (product_commuted_exponent)
open GaussianPolynomialExponentAlgebra (associative_reader commutative_jet left_distribution)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem reflexive_jet (P N H : PTm n) : Γ ⊢[PRAAx] jetEqual P N P N H := .allI (.impI (.eqRefl _))

theorem left_term (P Q A H E D e : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ H) (hQ : Γ ⊢[PRAAx] length Q ≐ succ E)
    (hA : Γ ⊢[PRAAx] length A ≐ succ D)
    (heH : Γ ⊢[PRAAx] le e H) (heE : Γ ⊢[PRAAx] le e E) (heD : Γ ⊢[PRAAx] le e D)
    (hJet : Γ ⊢[PRAAx] jetEqual (euler P H) H (product A P D H) (D+H) e) : Γ ⊢[PRAAx]
    exponentCoefficient (product (euler P H) Q H E) (H+E) e ≐
      exponentCoefficient (product A (product P Q H E) D (H+E)) (D+(H+E)) e :=
  (product_reader _ _ _ _ _ _ _ _ e e hJet (reflexive_jet Q E e) (le_refl e)
    heH heE (le_trans heD (le_add_right D H)) heE).eqTrans
      (associative_reader A P Q D H E e hA hP hQ heD)

theorem right_term (P Q B H E D e : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ H) (hQ : Γ ⊢[PRAAx] length Q ≐ succ E)
    (hB : Γ ⊢[PRAAx] length B ≐ succ D)
    (heH : Γ ⊢[PRAAx] le e H) (heE : Γ ⊢[PRAAx] le e E) (heD : Γ ⊢[PRAAx] le e D)
    (hJet : Γ ⊢[PRAAx] jetEqual (euler Q E) E (product B Q D E) (D+E) e) : Γ ⊢[PRAAx]
    exponentCoefficient (product P (euler Q E) H E) (H+E) e ≐
      exponentCoefficient (product B (product P Q H E) D (H+E)) (D+(H+E)) e :=
  (product_reader _ _ _ _ _ _ _ _ e e (reflexive_jet P H e) hJet (le_refl e)
    heH heE heH (le_trans heD (le_add_right D E))).eqTrans
      ((product_commuted_exponent P H (product B Q D E) (D+E) e hP (product_length _ _ _ _) heH).eqTrans
        ((associative_reader B Q P D E H e hB hQ hP heD).eqTrans
          (product_reader _ _ _ _ _ _ _ _ e e (reflexive_jet B D e)
            (commutative_jet Q P E H e hQ hP heE) (le_refl e)
            heD (le_trans heE (le_add_right E H)) heD (le_trans heH (le_add_right H E)))))

theorem original_product_Euler_factorization (P Q A B H E D e : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ H) (hQ : Γ ⊢[PRAAx] length Q ≐ succ E)
    (hA : Γ ⊢[PRAAx] length A ≐ succ D) (hB : Γ ⊢[PRAAx] length B ≐ succ D)
    (heH : Γ ⊢[PRAAx] le e H) (heE : Γ ⊢[PRAAx] le e E) (heD : Γ ⊢[PRAAx] le e D)
    (hJetP : Γ ⊢[PRAAx] jetEqual (euler P H) H (product A P D H) (D+H) e)
    (hJetQ : Γ ⊢[PRAAx] jetEqual (euler Q E) E (product B Q D E) (D+E) e) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (product P Q H E) (H+E)) (H+E) e ≐
      exponentCoefficient (product (added A B (succ D)) (product P Q H E) D (H+E)) (D+(H+E)) e := by
  have he : Γ ⊢[PRAAx] le e (H+E) := le_trans heH (le_add_right H E)
  have source := (exponent_inside (Γ := Γ) (euler (product P Q H E) (H+E)) (H+E) e he).eqTrans
    ((GaussianRationalEulerCoefficients.product_leibniz P Q H E e heH heE).eqTrans
      ((GaussianRationalPolynomialBuffers.added_lookup _ _ _ _
        ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))).eqTrans
          (qadd_congr (exponent_inside _ _ _ he).eqSymm (exponent_inside _ _ _ he).eqSymm)))
  exact source.eqTrans ((qadd_congr
    (left_term P Q A H E D e hP hQ hA heH heE heD hJetP)
    (right_term P Q B H E D e hP hQ hB heH heE heD hJetQ)).eqTrans
      (left_distribution A B (product P Q H E) D (H+E) e hA hB (product_length _ _ _ _) heD he).eqSymm)

def input (P Q A B H E D e : PTm n) : Fm PTm n :=
  length P ≐ succ H ⋏ (length Q ≐ succ E ⋏ (length A ≐ succ D ⋏ (length B ≐ succ D ⋏
    (le e H ⋏ (le e E ⋏ (le e D ⋏
      (jetEqual (euler P H) H (product A P D H) (D+H) e ⋏
        jetEqual (euler Q E) E (product B Q D E) (D+E) e)))))))

theorem from_input (P Q A B H E D e : PTm n) (h : Γ ⊢[PRAAx] input P Q A B H E D e) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (product P Q H E) (H+E)) (H+E) e ≐
      exponentCoefficient (product (added A B (succ D)) (product P Q H E) D (H+E)) (D+(H+E)) e :=
  original_product_Euler_factorization P Q A B H E D e h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂

theorem actual_finite_product_Euler_kernel_sum_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      exponentCoefficient (euler (product (var 0) (var 1) (var 4) (var 5)) (var 4+var 5)) (var 4+var 5) (var 7) ≐
        exponentCoefficient (product (added (var 2) (var 3) (succ (var 6)))
          (product (var 0) (var 1) (var 4) (var 5)) (var 6) (var 4+var 5)) (var 6+(var 4+var 5)) (var 7)) :=
  closeUniv 8 (.impI (from_input _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialProductEulerFactorization
