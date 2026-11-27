import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.FiniteProducts.GaussianBarnesCanonicalBaseProductShift
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Coefficients.GaussianGammaEulerFactorPolynomial
import IPRADerivations.Analysis.Polynomials.Products.Powers.GaussianRationalPolynomialPowers

/-!
# Rational coefficient polynomial for the original Barnes base powers

The coefficients and degree depend only on the kept cutoff. Evaluation
at the original rational input gives the exact folded base powers,
including when one or more of their bases vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomial

open_ipra
open GaussianBarnesCanonicalBaseProductShift (powerProduct powerBody power_at)
open GaussianBarnesCanonicalPolynomialShift (data)
open GaussianRationalFiniteProduct (product_zero product_succ)
open GaussianRationalHorner (evaluate ofGaussian)
open GaussianRationalMonicReduction (singleton singleton_evaluation singleton_length evaluate_congr)
open GaussianRationalPolynomialProduct (product product_length product_evaluation)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def degreeF : PR 2 := rec2 (zero : PTm 1) (var 1 + succ (var 0))
def degree (N : PTm n) : PTm n := ap2 degreeF N zero
def factor (i : PTm n) : PTm n :=
  GaussianRationalPolynomialPowers.power (GaussianGammaEulerFactorPolynomial.polynomial i) one (succ i)
def advance (i C : PTm n) : PTm n := product C (factor i) (degree i) (succ i)
private def stepBody : PTm 3 := advance (var 0) (var 1)
def polynomialF : PR 2 := rec2 (singleton qone : PTm 1) stepBody
def polynomial (N : PTm n) : PTm n := ap2 polynomialF N zero

@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (degree N) = degree (Syn.subst σ N) := by simp [degree]

@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (factor i) = factor (Syn.subst σ i) := by simp [factor]

@[simp] theorem subst_advance {m : ℕ} (σ : Fin n → PTm m) (i C : PTm n) :
    Syn.subst σ (advance i C) = advance (Syn.subst σ i) (Syn.subst σ C) := by simp [advance]

@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (polynomial N) = polynomial (Syn.subst σ N) := by simp [polynomial]

theorem degree_zero : Γ ⊢[PRAAx] degree (zero : PTm n) ≐ zero := by
  simpa [degree,degreeF] using rec2_zero (Γ := Γ) (zero : PTm 1) (var 1 + succ (var 0)) (zero : PTm n)

theorem degree_succ (N : PTm n) : Γ ⊢[PRAAx] degree (succ N) ≐ degree N + succ N := by
  have h := rec2_succ (Γ := Γ) (zero : PTm 1) (var 1 + succ (var 0)) N (zero : PTm n)
  simpa only [degree,degreeF,LeanProofs.IPRA.PTm.subst_add,ConciseIPRA.PTm.subst_succ,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using h

theorem polynomial_zero : Γ ⊢[PRAAx] polynomial (zero : PTm n) ≐ singleton qone := by
  simpa only [polynomial,polynomialF,GaussianRationalMonicReduction.subst_singleton,
    GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (singleton qone : PTm 1) stepBody (zero : PTm n)

theorem polynomial_succ (N : PTm n) : Γ ⊢[PRAAx] polynomial (succ N) ≐ advance N (polynomial N) := by
  simpa only [polynomial,polynomialF,stepBody,subst_advance,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using
    rec2_succ (Γ := Γ) (singleton qone : PTm 1) stepBody N (zero : PTm n)

theorem factor_length (i : PTm n) : Γ ⊢[PRAAx] length (factor i) ≐ succ (succ i) :=
  (GaussianRationalPolynomialPowers.power_length _ _ _).eqTrans (by ipra_ring)

theorem polynomial_length (N : PTm n) : Γ ⊢[PRAAx] length (polynomial N) ≐ succ (degree N) := by
  have all : Γ ⊢[PRAAx] .all (length (polynomial (var 0)) ≐ succ (degree (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_polynomial,ConciseIPRA.PTm.subst_succ,
        subst_degree,Syn.subst_var,Syn.inst_zero]
      exact ((congrFst polynomial_zero).eqTrans (singleton_length qone)).eqTrans
        (congrSucc degree_zero).eqSymm
    · simp only [Fm.subst_eq,subst_length,subst_polynomial,ConciseIPRA.PTm.subst_succ,
        subst_degree,Syn.subst_var,Syn.repl_zero]
      exact (congrFst (polynomial_succ (var 0))).eqTrans
        ((product_length _ _ _ _).eqTrans (congrSucc (degree_succ (var 0))).eqSymm)
  simpa only [Fm.subst_eq,subst_length,subst_polynomial,ConciseIPRA.PTm.subst_succ,
    subst_degree,Syn.subst_var,Syn.inst_zero] using all.allE N

theorem factor_evaluation (i z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (factor i) (ofGaussian z B) ≐ GaussianBarnesCanonicalFactor.powerValue z B (succ i) := by
  have e := GaussianGammaEulerFactorPolynomial.original_factor_evaluation i z B hB
  exact (GaussianRationalPolynomialPowers.power_evaluation _ one (succ i) _
    (GaussianGammaEulerFactorPolynomial.polynomial_length i)).eqTrans
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl (succ i)) e)

private def evaluationLaw (z B N : PTm n) : Fm PTm n :=
  evaluate (polynomial N) (ofGaussian z B) ≐ powerProduct z B N

@[simp] private theorem subst_evaluationLaw {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    (evaluationLaw z B N).subst σ =
      evaluationLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [evaluationLaw]

private theorem evaluation_zero (z B : PTm n) : Γ ⊢[PRAAx] evaluationLaw z B zero :=
  (evaluate_congr polynomial_zero (.eqRefl _)).eqTrans
    ((singleton_evaluation qone _).eqTrans
      ((GaussianTranslatedNonconstant.recode_eq _ qone_canonical).eqTrans
        (product_zero powerBody (data z B)).eqSymm))

private theorem evaluation_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] evaluationLaw z B N) : Γ ⊢[PRAAx] evaluationLaw z B (succ N) :=
  (evaluate_congr (polynomial_succ N) (.eqRefl _)).eqTrans
    ((product_evaluation _ _ _ _ _ (polynomial_length N) (factor_length N)).eqTrans
      ((qmul_congr ih ((factor_evaluation N z B hB).eqTrans (power_at N z B).eqSymm)).eqTrans
        (product_succ powerBody N (data z B)).eqSymm))

theorem original_evaluation (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (polynomial N) (ofGaussian z B) ≐ powerProduct z B N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift z) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact evaluation_zero z B
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact evaluation_step _ _ _ bs.wk Prf.hyp0
  change Γ ⊢[PRAAx] evaluationLaw z B N
  simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem actual_Barnes_head_polynomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ evaluate (polynomial (var 2)) (ofGaussian (var 0) (var 1)) ≐
      powerProduct (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (original_evaluation _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomial
