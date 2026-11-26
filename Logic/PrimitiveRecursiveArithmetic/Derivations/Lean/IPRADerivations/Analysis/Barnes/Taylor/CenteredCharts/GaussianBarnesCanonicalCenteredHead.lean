import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadPolynomialDerivative
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerFactorPolynomial
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialPowers

/-!
# Centered coefficient buffer for the original Barnes base powers

The constant coefficient of each linear factor is the original base
at the center. Its linear coefficient is the reciprocal of its index.
The finite fold is valid even at a zero of the kept product.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredHead

open_ipra
open GaussianBarnesCanonicalBaseProductShift (powerProduct powerBody power_at)
open GaussianBarnesCanonicalPolynomialShift (data)
open GaussianBarnesCanonicalHeadPolynomial (degree degree_zero degree_succ)
open ComplexLogarithmRemainder (add)
open GaussianRationalFiniteProduct (product_zero product_succ)
open GaussianRationalHorner (evaluate ofGaussian qadd qmul)
open GaussianBarnesCanonicalFactor (base powerValue)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianGammaExponentStep (reciprocal_times_point)
open GaussianGammaLinearCoefficient (monomial_length monomial_evaluation)
open GaussianRationalPolynomialBuffers (added_length added_evaluation leftPad pad_length pad_evaluation)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianRationalMonicReduction (singleton singleton_evaluation singleton_length evaluate_congr)
open GaussianRationalPolynomialProduct (product product_length product_evaluation)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linear (z B i : PTm n) : PTm n :=
  GaussianRationalPolynomialBuffers.added
    (GaussianGammaLinearCoefficient.monomial (GaussianGammaHarmonicIncrement.reciprocalPoint i))
    (GaussianRationalPolynomialBuffers.leftPad
      (singleton (GaussianBarnesCanonicalFactor.base z B (succ i))) one) two

def factor (z B i : PTm n) : PTm n :=
  GaussianRationalPolynomialPowers.power (linear z B i) one (succ i)
def advance (z B i C : PTm n) : PTm n := product C (factor z B i) (degree i) (succ i)
private def stepBody : PTm 3 := advance (fstT (var 2)) (sndT (var 2)) (var 0) (var 1)
def polynomialF : PR 2 := rec2 (singleton qone : PTm 1) stepBody
def polynomial (z B N : PTm n) : PTm n := ap2 polynomialF N (pairT z B)

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (z B i : PTm n) :
    Syn.subst σ (linear z B i) = linear (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) := by simp [linear]

@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (z B i : PTm n) :
    Syn.subst σ (factor z B i) = factor (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) := by simp [factor]

@[simp] theorem subst_advance {m : ℕ} (σ : Fin n → PTm m) (z B i C : PTm n) :
    Syn.subst σ (advance z B i C) = advance (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) (Syn.subst σ C) := by simp [advance]

@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (polynomial z B N) = polynomial (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [polynomial]

theorem polynomial_zero (z B : PTm n) : Γ ⊢[PRAAx] polynomial z B zero ≐ singleton qone := by
  simpa only [polynomial,polynomialF,GaussianRationalMonicReduction.subst_singleton,
    GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (singleton qone : PTm 1) stepBody (pairT z B)

theorem polynomial_succ (z B N : PTm n) :
    Γ ⊢[PRAAx] polynomial z B (succ N) ≐ advance z B N (polynomial z B N) := by
  let x := pairT z B
  have raw : Γ ⊢[PRAAx] polynomial z B (succ N) ≐ advance (fstT x) (sndT x) N (polynomial z B N) := by
    simpa only [polynomial,polynomialF,stepBody,subst_advance,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      rec2_succ (Γ := Γ) (singleton qone : PTm 1) stepBody N x
  have read : Γ ⊢[PRAAx] advance (fstT x) (sndT x) N (polynomial z B N) ≐ advance z B N (polynomial z B N) := by
    ipra_congr (advance (var 0) (var 1) (var 2) (var 3) : PTm 4) with [fst_pair z B,snd_pair z B,.eqRefl _,.eqRefl _]
  exact raw.eqTrans read

theorem factor_length (z B i : PTm n) : Γ ⊢[PRAAx] length (factor z B i) ≐ succ (succ i) :=
  (GaussianRationalPolynomialPowers.power_length _ _ _).eqTrans (by ipra_ring)

theorem polynomial_length (z B N : PTm n) : Γ ⊢[PRAAx] length (polynomial z B N) ≐ succ (degree N) := by
  have all : Γ ⊢[PRAAx] .all (length (polynomial (Syn.shift z) (Syn.shift B) (var 0)) ≐ succ (degree (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_polynomial,ConciseIPRA.PTm.subst_succ,
        GaussianBarnesCanonicalHeadPolynomial.subst_degree,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact ((congrFst (polynomial_zero z B)).eqTrans (singleton_length qone)).eqTrans
        (congrSucc degree_zero).eqSymm
    · simp only [Fm.subst_eq,subst_length,subst_polynomial,ConciseIPRA.PTm.subst_succ,
        GaussianBarnesCanonicalHeadPolynomial.subst_degree,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (polynomial_succ _ _ (var 0))).eqTrans
        ((product_length _ _ _ _).eqTrans (congrSucc (degree_succ (var 0))).eqSymm)
  simpa only [Fm.subst_eq,subst_length,subst_polynomial,ConciseIPRA.PTm.subst_succ,
    GaussianBarnesCanonicalHeadPolynomial.subst_degree,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N


theorem linear_evaluation (z h B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] evaluate (linear z B i) (ofGaussian h B) ≐ base (add z h) B (succ i) := by
  let c := base z B (succ i)
  let w := ofGaussian h B
  let t := ofGaussian z B
  let a := reciprocalPoint i
  let u := ofGaussian z (B*succ i)
  have hc : Γ ⊢[PRAAx] length (leftPad (singleton c) one) ≐ two :=
    (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (singleton_length c)).eqTrans (by ipra_ring))
  have cv : Γ ⊢[PRAAx] evaluate (leftPad (singleton c) one) w ≐ c :=
    (pad_evaluation _ _ _).eqTrans ((singleton_evaluation c w).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (GaussianRationalHorner.qadd_canonical _ _)))
  have split : Γ ⊢[PRAAx] evaluate (linear z B i) w ≐ qadd (qmul a w) c :=
    (added_evaluation _ _ _ _ (monomial_length _) hc).eqTrans
      (qadd_congr (monomial_evaluation a w) cv)
  have combine : Γ ⊢[PRAAx] qadd (qmul a w) c ≐ qadd qone (qmul a (qadd t w)) :=
    (qadd_commutative _ _).eqTrans ((qadd_associative qone u (qmul a w)).eqTrans
      (qadd_congr (.eqRefl _) ((qadd_congr (reciprocal_times_point z B i hB).eqSymm (.eqRefl _)).eqTrans
        (qmul_add a t w).eqSymm)))
  exact split.eqTrans (combine.eqTrans
    (qadd_congr (.eqRefl _) ((qmul_congr (.eqRefl _)
      (GaussianBarnesCanonicalHeadPolynomialDerivative.argument_add z h B hB)).eqTrans
        (reciprocal_times_point (add z h) B i hB))))

theorem factor_evaluation (i z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (factor z B i) (ofGaussian h B) ≐ powerValue (add z h) B (succ i) :=
  (GaussianRationalPolynomialPowers.power_evaluation _ one (succ i) _ (added_length _ _ _)).eqTrans
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (linear_evaluation z h B i hB))

private def evaluationLaw (z h B N : PTm n) : Fm PTm n :=
  evaluate (polynomial z B N) (ofGaussian h B) ≐ powerProduct (add z h) B N

@[simp] private theorem subst_evaluationLaw {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    (evaluationLaw z h B N).subst σ =
      evaluationLaw (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by simp [evaluationLaw]

private theorem evaluation_zero (z h B : PTm n) : Γ ⊢[PRAAx] evaluationLaw z h B zero :=
  (evaluate_congr (polynomial_zero z B) (.eqRefl _)).eqTrans
    ((singleton_evaluation qone _).eqTrans
      ((GaussianTranslatedNonconstant.recode_eq _ qone_canonical).eqTrans
        (product_zero powerBody (data (add z h) B)).eqSymm))

private theorem evaluation_step (z h B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] evaluationLaw z h B N) : Γ ⊢[PRAAx] evaluationLaw z h B (succ N) :=
  (evaluate_congr (polynomial_succ z B N) (.eqRefl _)).eqTrans
    ((product_evaluation _ _ _ _ _ (polynomial_length z B N) (factor_length z B N)).eqTrans
      ((qmul_congr ih ((factor_evaluation N z h B hB).eqTrans (power_at N (add z h) B).eqSymm)).eqTrans
        (product_succ powerBody N (data (add z h) B)).eqSymm))

theorem original_evaluation (z h B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (polynomial z B N) (ofGaussian h B) ≐ powerProduct (add z h) B N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift z) (Syn.shift h) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact evaluation_zero z h B
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact evaluation_step _ _ _ _ bs.wk Prf.hyp0
  change Γ ⊢[PRAAx] evaluationLaw z h B N
  simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem actual_Barnes_kept_powers_centered_polynomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ evaluate (polynomial (var 0) (var 2) (var 3)) (ofGaussian (var 1) (var 2)) ≐
      powerProduct (add (var 0) (var 1)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (original_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredHead
