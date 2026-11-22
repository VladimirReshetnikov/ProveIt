import IPRADerivations.Analysis.GaussianGammaEulerFactorPolynomial

/-!
# Actual coefficients of the original Euler polynomial head

A primitive-recursive coefficient-buffer convolution starts at X and
multiplies the unchanged original factor polynomials 1+X/k. Genuine
internal induction binds its Horner value to the original EulerHead.head
and bounds its weighted coefficient mass by R(1+R)^N at every internal N.
No value or coefficient law for the constructed buffer is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul evaluate ofGaussian)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianGammaLinearCoefficient (monomial)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalSyntheticBounds (natCode)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def advance (N C : PTm n) : PTm n := GaussianRationalPolynomialProduct.product C
  (GaussianGammaEulerFactorPolynomial.polynomial N) (succ N) one
def stepBody : PTm 3 := advance (var 0) (var 1)
def headF : PR 2 := rec2 (monomial qone : PTm 1) stepBody
def polynomial (N : PTm n) : PTm n := ap2 headF N zero
@[simp] theorem subst_advance {m : ℕ} (σ : Fin n → PTm m) (N C : PTm n) :
    Syn.subst σ (advance N C) = advance (Syn.subst σ N) (Syn.subst σ C) := by simp [advance]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (polynomial N) = polynomial (Syn.subst σ N) := by simp [polynomial]

theorem polynomial_zero : Γ ⊢[PRAAx] polynomial (zero : PTm n) ≐ monomial qone := by
  simpa only [polynomial,headF,GaussianGammaLinearCoefficient.subst_monomial,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (monomial qone : PTm 1) stepBody (zero : PTm n)
theorem polynomial_succ (N : PTm n) : Γ ⊢[PRAAx] polynomial (succ N) ≐ advance N (polynomial N) := by
  simpa only [polynomial,headF,stepBody,subst_advance,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] using
    rec2_succ (Γ := Γ) (monomial qone : PTm 1) stepBody N (zero : PTm n)

theorem polynomial_length (N : PTm n) : Γ ⊢[PRAAx] length (polynomial N) ≐ succ (succ N) := by
  have all : Γ ⊢[PRAAx] .all (length (polynomial (var 0)) ≐ succ (succ (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,LeanProofs.IPRA.Foundations.SequenceComposition.subst_length,
        subst_polynomial,PTm.subst_succ,Syn.subst_var,Syn.inst_zero]
      exact (congrFst polynomial_zero).eqTrans (GaussianGammaLinearCoefficient.monomial_length qone)
    · simp only [Fm.subst_eq,LeanProofs.IPRA.Foundations.SequenceComposition.subst_length,
        subst_polynomial,PTm.subst_succ,Syn.subst_var,Syn.repl_zero]
      exact (congrFst (polynomial_succ (var 0))).eqTrans
        ((GaussianRationalPolynomialProduct.product_length _ _ _ _).eqTrans (by ipra_ring))
  simpa only [Fm.subst_eq,LeanProofs.IPRA.Foundations.SequenceComposition.subst_length,
    subst_polynomial,PTm.subst_succ,Syn.subst_var,Syn.inst_zero] using all.allE N

def evaluationLaw (z B N : PTm n) : Fm PTm n := evaluate (polynomial N) (ofGaussian z B) ≐ GaussianGammaEulerHead.head z B N
@[simp] theorem subst_evaluationLaw {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    (evaluationLaw z B N).subst σ = evaluationLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [evaluationLaw]

theorem evaluation_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] evaluationLaw z B zero :=
  (GaussianRationalMonicReduction.evaluate_congr polynomial_zero (.eqRefl _)).eqTrans
    ((GaussianGammaLinearCoefficient.monomial_evaluation qone _).eqTrans
      ((GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB)).eqTrans
        (GaussianGammaEulerHead.head_zero z B hB).eqSymm))

theorem evaluation_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] evaluationLaw z B N) : Γ ⊢[PRAAx] evaluationLaw z B (succ N) := by
  have source := GaussianRationalMonicReduction.evaluate_congr (Γ := Γ) (polynomial_succ N) (.eqRefl (ofGaussian z B))
  exact source.eqTrans ((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _
    (polynomial_length N) (GaussianGammaEulerFactorPolynomial.polynomial_length N)).eqTrans
      ((qmul_congr ih (GaussianGammaEulerFactorPolynomial.original_factor_evaluation N z B hB)).eqTrans
        (GaussianGammaEulerHead.head_succ z B N).eqSymm))

theorem original_head_evaluation (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] evaluationLaw z B N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift z) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact evaluation_zero z B hB
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact evaluation_step _ _ _ bs.wk Prf.hyp0
  simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def massLaw (R N : PTm n) : Fm PTm n := rationalLE
  (weightedNorm (polynomial N) (succ N) (radiusPoint R one)) (natCode (R*pw (one+R) N))
@[simp] theorem subst_massLaw {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    (massLaw R N).subst σ = massLaw (Syn.subst σ R) (Syn.subst σ N) := by simp [massLaw]

theorem mass_zero (R : PTm n) : Γ ⊢[PRAAx] massLaw R zero := by
  have first := GaussianGammaLinearCoefficient.monomial_weighted_bound (Γ := Γ) qone R
  have budget := (RationalAlgebra.multiply_congr (Γ := Γ) GaussianRationalSyntheticBounds.qL1_qone (.eqRefl (natCode R))).eqTrans
    ((GaussianRationalSyntheticBounds.natCode_multiply one R).eqTrans
      (GaussianPositiveExponentialMajorant.natCode_congr (show Γ ⊢[PRAAx] one*R ≐ R*pw (one+R) zero by
        have e := natEq (pw_zero (Γ := Γ) (one+R)); apply deriveNat; ipra_simps; rw [e]; ring)))
  exact RationalArgmin.rationalLE_congr
    (GaussianFiniteExponentialWeightedNorm.weighted_congr polynomial_zero.eqSymm (.eqRefl _) (.eqRefl _)) budget first

theorem mass_step (R N : PTm n) (ih : Γ ⊢[PRAAx] massLaw R N) : Γ ⊢[PRAAx] massLaw R (succ N) := by
  have first := GaussianRationalPolynomialDilation.weighted_product_bound (Γ := Γ)
    (polynomial N) (GaussianGammaEulerFactorPolynomial.polynomial N) (succ N) one (radiusPoint R one)
    (polynomial_length N) (GaussianGammaEulerFactorPolynomial.polynomial_length N)
  have second := GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _
    (GaussianFiniteExponentialWeightedNorm.weighted_nonnegative _ _ _)
    (GaussianRationalSyntheticBounds.natCode_nonnegative _) ih (GaussianGammaEulerFactorPolynomial.polynomial_mass N R)
  have budget := (GaussianRationalSyntheticBounds.natCode_multiply (Γ := Γ) (R*pw (one+R) N) (one+R)).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (show Γ ⊢[PRAAx] (R*pw (one+R) N)*(one+R) ≐ R*pw (one+R) (succ N) by
      have e := natEq (pw_succ (Γ := Γ) (one+R) N); apply deriveNat; ipra_simps; rw [e]; ring))
  exact RationalArgmin.rationalLE_congr
    (GaussianFiniteExponentialWeightedNorm.weighted_congr (polynomial_succ N).eqSymm (by ipra_ring) (.eqRefl _)) budget
      (RationalArgmin.transitive first second)

theorem original_head_coefficient_mass (R N : PTm n) : Γ ⊢[PRAAx] massLaw R N := by
  have all : Γ ⊢[PRAAx] .all (massLaw (Syn.shift R) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_massLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact mass_zero R
    · simp only [subst_massLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact mass_step _ _ Prf.hyp0
  simpa only [subst_massLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem original_Euler_head_coefficient_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ evaluationLaw (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (original_head_evaluation _ _ _ Prf.hyp0))
theorem original_Euler_head_coefficient_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (massLaw (var 0) (var 1)) :=
  closeUniv 2 (original_head_coefficient_mass _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadPolynomial
