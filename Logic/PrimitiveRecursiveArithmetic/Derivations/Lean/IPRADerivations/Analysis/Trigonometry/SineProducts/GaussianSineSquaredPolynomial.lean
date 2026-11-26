import IPRADerivations.Analysis.Trigonometry.MultipleAngles.GaussianSineMultipleAngleRecurrence
import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMonicCompanion
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalReconstruction

/-!
# Monic polynomials for the even multiple-angle recurrence

The actual Horner rows use the squared trace Y, with initial rows 1
and Y−1. Each step multiplies the newer row by Y−2 and subtracts the
older row after padding it on the left. The length and leading entry
are derived for every runtime index.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSquaredPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientL1 (subCoefficients sub_lookup subst_subCoefficients)
open GaussianRationalHorner (qmul canonical evaluate)
open GaussianRationalLinearProduct (linear linear_length linear_evaluation linear_lookup linear_canonical padded_inside delayed_zero)
open GaussianRationalMetric (qsub)
open GaussianRationalMonicCompanion (sub_length difference_evaluation)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup singleton_evaluation evaluate_congr
  canonical_coefficients_congr)
open GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation pad_leading)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_zero_right qmul_congr qsub_congr canonicalCoefficients)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianSineMultipleAngleRecurrence (twoPoint evenValue even_zero even_one even_recurrence)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def seed : PTm n := linear (singleton qone) qone one
def next (P Q J : PTm n) : PTm n :=
  subCoefficients (linear Q twoPoint (succ (succ J))) (leftPad P two) (succ (succ (succ J)))

@[simp] theorem subst_seed {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (seed : PTm n) = (seed : PTm m) := by simp [seed]
@[simp] theorem subst_next {m : ℕ} (σ : Fin n → PTm m) (P Q J : PTm n) :
    Syn.subst σ (next P Q J) = next (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ J) := by
  simp [next,twoPoint]

def baseBody : PTm 1 := pairT (singleton qone) seed
def stepBody : PTm 3 := pairT (sndT (var 1)) (next (fstT (var 1)) (sndT (var 1)) (var 0))
def stateF : PR 2 := rec2 baseBody stepBody
def state (J : PTm n) : PTm n := ap2 stateF J zero
def coefficients (J : PTm n) : PTm n := fstT (state J)
def following (J : PTm n) : PTm n := sndT (state J)

@[simp] theorem subst_state {m : ℕ} (σ : Fin n → PTm m) (J : PTm n) :
    Syn.subst σ (state J) = state (Syn.subst σ J) := by simp [state]
@[simp] theorem subst_coefficients {m : ℕ} (σ : Fin n → PTm m) (J : PTm n) :
    Syn.subst σ (coefficients J) = coefficients (Syn.subst σ J) := by simp [coefficients]
@[simp] theorem subst_following {m : ℕ} (σ : Fin n → PTm m) (J : PTm n) :
    Syn.subst σ (following J) = following (Syn.subst σ J) := by simp [following]

theorem state_zero : Γ ⊢[PRAAx] state (zero : PTm n) ≐ pairT (singleton qone) seed := by
  simpa [state,stateF,baseBody] using rec2_zero (Γ := Γ) baseBody stepBody (zero : PTm n)
theorem state_succ (J : PTm n) :
    Γ ⊢[PRAAx] state (succ J) ≐ pairT (following J) (next (coefficients J) (following J) J) := by
  simpa only [state,stateF,stepBody,coefficients,following,subst_pairT,subst_sndT,subst_fstT,subst_next,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] using rec2_succ (Γ := Γ) baseBody stepBody J zero
theorem coefficients_zero : Γ ⊢[PRAAx] coefficients (zero : PTm n) ≐ singleton qone :=
  (congrFst state_zero).eqTrans (fst_pair _ _)
theorem following_zero : Γ ⊢[PRAAx] following (zero : PTm n) ≐ seed :=
  (congrSnd state_zero).eqTrans (snd_pair _ _)
theorem coefficients_succ (J : PTm n) : Γ ⊢[PRAAx] coefficients (succ J) ≐ following J :=
  (congrFst (state_succ J)).eqTrans (fst_pair _ _)
theorem following_succ (J : PTm n) :
    Γ ⊢[PRAAx] following (succ J) ≐ next (coefficients J) (following J) J :=
  (congrSnd (state_succ J)).eqTrans (snd_pair _ _)

private theorem linear_leading_one (C z N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] entry (linear C z N) zero ≐ qone :=
  (linear_lookup C z N zero (zero_le N)).eqTrans
    ((qsub_congr ((padded_inside C N zero hN).eqTrans h)
      ((qmul_congr (delayed_zero C N) (.eqRefl z)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left z))).eqTrans
      (GaussianRationalReconstruction.qsub_zero_right qone qone_canonical))

private theorem next_leading (P Q J : PTm n) (h : Γ ⊢[PRAAx] entry Q zero ≐ qone) :
    Γ ⊢[PRAAx] entry (next P Q J) zero ≐ qone :=
  (sub_lookup _ _ _ _ (zero_lt_succ _)).eqTrans
    ((qsub_congr (linear_leading_one Q twoPoint (succ (succ J)) (zero_lt_succ _) h)
      (pad_leading P two zero (le_succ_self one))).eqTrans
      (GaussianRationalReconstruction.qsub_zero_right qone qone_canonical))

def shape (J : PTm n) : Fm PTm n :=
  (length (coefficients J) ≐ succ J ⋏ entry (coefficients J) zero ≐ qone) ⋏
    (length (following J) ≐ succ (succ J) ⋏ entry (following J) zero ≐ qone)

@[simp] theorem subst_shape {m : ℕ} (σ : Fin n → PTm m) (J : PTm n) :
    (shape J).subst σ = shape (Syn.subst σ J) := by simp [shape]

private theorem shape_zero : Γ ⊢[PRAAx] shape (zero : PTm n) :=
  .andI
    (.andI ((congrFst coefficients_zero).eqTrans (singleton_length _))
      ((entry_congr coefficients_zero (.eqRefl _)).eqTrans (singleton_lookup _)))
    (.andI ((congrFst following_zero).eqTrans (linear_length _ _ _))
      ((entry_congr following_zero (.eqRefl _)).eqTrans
        (linear_leading_one _ _ _ (le_refl one) (singleton_lookup _))))

private theorem shape_succ (J : PTm n) (h : Γ ⊢[PRAAx] shape J) : Γ ⊢[PRAAx] shape (succ J) :=
  .andI
    (.andI ((congrFst (coefficients_succ J)).eqTrans h.andE₂.andE₁)
      ((entry_congr (coefficients_succ J) (.eqRefl _)).eqTrans h.andE₂.andE₂))
    (.andI ((congrFst (following_succ J)).eqTrans (sub_length _ _ _))
      ((entry_congr (following_succ J) (.eqRefl _)).eqTrans (next_leading _ _ _ h.andE₂.andE₂)))

theorem polynomial_shape (J : PTm n) : Γ ⊢[PRAAx] shape J := by
  have all : Γ ⊢[PRAAx] .all (shape (var 0)) := by
    refine PRA.qfInd _ ⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩ ?_ ?_
    · simpa only [subst_shape,Syn.subst_var,Syn.inst_zero] using (shape_zero (Γ := Γ))
    · simpa only [subst_shape,Syn.subst_var,Syn.repl_zero] using
        (shape_succ (var 0 : PTm (n+1)) (Prf.hyp0 : shape (var 0) :: Γ.map Fm.shift ⊢[PRAAx] shape (var 0)))
  simpa only [subst_shape,Syn.subst_var,Syn.inst_zero] using all.allE J

theorem coefficients_length (J : PTm n) : Γ ⊢[PRAAx] length (coefficients J) ≐ succ J :=
  (polynomial_shape J).andE₁.andE₁
theorem coefficients_monic (J : PTm n) : Γ ⊢[PRAAx] entry (coefficients J) zero ≐ qone :=
  (polynomial_shape J).andE₁.andE₂

theorem following_canonical (J : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (following J) := by
  refine .orE (zero_or_succ J) ?_ ?_
  · exact canonical_coefficients_congr
      ((congrSnd (congrAp2 stateF Prf.hyp0 (.eqRefl zero))).eqTrans following_zero)
      (linear_canonical _ _ _)
  · exact canonical_coefficients_congr
      ((congrSnd (congrAp2 stateF Prf.hyp0 (.eqRefl zero))).eqTrans (following_succ (pred J)))
      (GaussianPolynomialMonicCompanion.difference_canonical _ _ _)

theorem coefficients_canonical (J : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (coefficients J) := by
  refine .orE (zero_or_succ J) ?_ ?_
  · exact canonical_coefficients_congr
      ((congrFst (congrAp2 stateF Prf.hyp0 (.eqRefl zero))).eqTrans coefficients_zero)
      GaussianRationalReconstruction.singleton_canonical
  · exact canonical_coefficients_congr
      ((congrFst (congrAp2 stateF Prf.hyp0 (.eqRefl zero))).eqTrans (coefficients_succ (pred J)))
      (following_canonical _)

private theorem one_evaluation (z : PTm n) : Γ ⊢[PRAAx] evaluate (singleton qone) z ≐ qone :=
  (singleton_evaluation _ _).eqTrans (GaussianTranslatedNonconstant.recode_eq _ qone_canonical)

theorem seed_evaluation (z : PTm n) : Γ ⊢[PRAAx] evaluate seed z ≐ qsub z qone :=
  (linear_evaluation _ _ _ _ (singleton_length _) GaussianRationalReconstruction.singleton_canonical).eqTrans
    ((qmul_congr (.eqRefl _) (one_evaluation z)).eqTrans
      (qmul_one_right _ (GaussianRationalMetric.qsub_canonical _ _)))

theorem next_evaluation (P Q J z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ J)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ (succ J)) (hc : Γ ⊢[PRAAx] canonicalCoefficients Q) :
    Γ ⊢[PRAAx] evaluate (next P Q J) z ≐ qsub (qmul (qsub z twoPoint) (evaluate Q z)) (evaluate P z) := by
  have pad : Γ ⊢[PRAAx] length (leftPad P two) ≐ succ (succ (succ J)) :=
    (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) hP).eqTrans (by ipra_ring))
  exact (difference_evaluation _ _ _ _ (linear_length _ _ _) pad).eqTrans
    (qsub_congr (linear_evaluation _ _ _ _ hQ hc) (pad_evaluation P two z))

def evaluationLaw (S J : PTm n) : Fm PTm n :=
  (evaluate (coefficients J) (qmul S S) ≐ evenValue S J) ⋏
    (evaluate (following J) (qmul S S) ≐ evenValue S (succ J))

@[simp] theorem subst_evaluationLaw {m : ℕ} (σ : Fin n → PTm m) (S J : PTm n) :
    (evaluationLaw S J).subst σ = evaluationLaw (Syn.subst σ S) (Syn.subst σ J) := by
  simp [evaluationLaw,evenValue]

private theorem evaluation_zero (S : PTm n) (hS : Γ ⊢[PRAAx] canonical S) :
    Γ ⊢[PRAAx] evaluationLaw S zero :=
  .andI ((evaluate_congr coefficients_zero (.eqRefl _)).eqTrans
      ((one_evaluation _).eqTrans (even_zero S).eqSymm))
    ((evaluate_congr following_zero (.eqRefl _)).eqTrans
      ((seed_evaluation _).eqTrans (even_one S hS).eqSymm))

private theorem evaluation_succ (S J : PTm n) (h : Γ ⊢[PRAAx] evaluationLaw S J) :
    Γ ⊢[PRAAx] evaluationLaw S (succ J) := by
  have dims := polynomial_shape (Γ := Γ) J
  have eval := next_evaluation (coefficients J) (following J) J (qmul S S) dims.andE₁.andE₁ dims.andE₂.andE₁
    (following_canonical J)
  exact .andI ((evaluate_congr (coefficients_succ J) (.eqRefl _)).eqTrans h.andE₂)
    ((evaluate_congr (following_succ J) (.eqRefl _)).eqTrans
      (eval.eqTrans ((qsub_congr (qmul_congr (.eqRefl _) h.andE₂) h.andE₁).eqTrans
        (even_recurrence S J).eqSymm)))

theorem evaluation_square (S J : PTm n) (hS : Γ ⊢[PRAAx] canonical S) :
    Γ ⊢[PRAAx] evaluate (coefficients J) (qmul S S) ≐ evenValue S J := by
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift S) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using evaluation_zero S hS
    · simpa only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        evaluation_succ (Syn.shift S) (var 0) (Prf.hyp0 :
          evaluationLaw (Syn.shift S) (var 0) :: Γ.map Fm.shift ⊢[PRAAx] evaluationLaw (Syn.shift S) (var 0))
  have hs : Γ ⊢[PRAAx] evaluationLaw S J := by
    simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE J
  exact hs.andE₁

theorem actual_sine_squared_trace_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (coefficients (var 0)) ≐ succ (var 0) ⋏
      (entry (coefficients (var 0)) zero ≐ qone ⋏ canonicalCoefficients (coefficients (var 0)))) :=
  closeUniv 1 (.andI (coefficients_length _) (.andI (coefficients_monic _) (coefficients_canonical _)))

theorem actual_sine_squared_trace_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (var 0) ⟶
      evaluate (coefficients (var 1)) (qmul (var 0) (var 0)) ≐ evenValue (var 0) (var 1)) :=
  closeUniv 2 (.impI (evaluation_square _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineSquaredPolynomial
