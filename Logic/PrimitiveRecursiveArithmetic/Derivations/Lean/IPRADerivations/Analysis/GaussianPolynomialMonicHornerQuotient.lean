import IPRADerivations.Analysis.GaussianPolynomialMonicHornerReduction
import IPRADerivations.Analysis.GaussianPolynomialYShift

/-!
# The quotient in polynomial-valued monic Horner division

The quotient recurrence appends the top row of the actual remainder at
each step. At arbitrary queries the evaluations of these two computed
polynomials reconstruct the original Horner prefix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialMonicHornerQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate horner hornerF qzero qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right qzero_add qzero_canonical)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at companion values values_length values_lookup monicValues
  values_congr evaluation_congr companion_evaluation)
open GaussianPolynomialMultiplicationMatrix (stored storedSyntax formula_stored stored_congr companion_stored)
open GaussianPolynomialConstantInjection (inject inject_stored inject_evaluation fields)
open GaussianPolynomialYShift (shiftY shift_stored shift_evaluation)
open GaussianPolynomialMonicHornerReduction (width zeroRows data data_fields stage stage_zero stage_succ stage_shape
  zero_rows_stored zero_rows_evaluation)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def advance (F H m a c j Q : PTm n) : PTm n :=
  inject (shiftY Q (succ j) (width a c j) c) (entry (stage F H m a c j) zero) (succ (succ j)) (width a c j) c

def initial : PTm 1 := zeroRows one (fields (var 0) 3)
def stepBody : PTm 3 := advance (fields (var 2) 0) (fields (var 2) 1) (fields (var 2) 2)
  (fields (var 2) 3) (fields (var 2) 4) (var 0) (var 1)
def quotientF : PR 2 := rec2 initial stepBody
def quotient (F H m a c j : PTm n) : PTm n := ap2 quotientF j (data F H m a c)

@[simp] theorem subst_advance {k : ℕ} (σ : Fin n → PTm k) (F H m a c j Q : PTm n) :
    Syn.subst σ (advance F H m a c j Q) = advance (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) (Syn.subst σ Q) := by simp [advance]
@[simp] theorem subst_quotient {k : ℕ} (σ : Fin n → PTm k) (F H m a c j : PTm n) :
    Syn.subst σ (quotient F H m a c j) = quotient (Syn.subst σ F) (Syn.subst σ H)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [quotient]

private theorem advance_parameters (p : PTm n) (F H m a c j Q : PTm n)
    (h : ∀ i : Fin 5, Γ ⊢[PRAAx] fields p i ≐ ![F,H,m,a,c] i) :
    Γ ⊢[PRAAx] advance (fields p 0) (fields p 1) (fields p 2) (fields p 3) (fields p 4) j Q ≐ advance F H m a c j Q := by
  simpa [Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    Prf.eqCongr (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![fields p 0,fields p 1,fields p 2,fields p 3,fields p 4,j,Q]) (σ' := ![F,H,m,a,c,j,Q])
      (fun i => by fin_cases i; exact h 0; exact h 1; exact h 2; exact h 3; exact h 4; exact .eqRefl _; exact .eqRefl _)

theorem quotient_zero (F H m a c : PTm n) : Γ ⊢[PRAAx] quotient F H m a c zero ≐ zeroRows one a := by
  have base := rec2_zero (Γ := Γ) initial stepBody (data F H m a c)
  simp only [initial,GaussianPolynomialMonicHornerReduction.subst_zeroRows,
    GaussianPolynomialConstantInjection.subst_fields,Syn.subst_var,
    one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] at base
  have widthField : Γ ⊢[PRAAx] fields (data F H m a c) 3 ≐ a := by simpa using data_fields F H m a c 3
  have e : Γ ⊢[PRAAx] zeroRows one (fields (data F H m a c) 3) ≐ zeroRows one a := by
    simpa using Prf.eqCongr (Γ := Γ) (zeroRows one (var 0) : PTm 1)
      (σ := ![fields (data F H m a c) 3]) (σ' := ![a]) (fun i => by fin_cases i; exact widthField)
  exact base.eqTrans e

theorem quotient_succ (F H m a c j : PTm n) : Γ ⊢[PRAAx]
    quotient F H m a c (succ j) ≐ advance F H m a c j (quotient F H m a c j) := by
  have e := rec2_succ (Γ := Γ) initial stepBody j (data F H m a c)
  simp only [stepBody,subst_advance,GaussianPolynomialConstantInjection.subst_fields,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  exact e.eqTrans (advance_parameters _ _ _ _ _ _ _ _ (data_fields F H m a c))

theorem quotient_stored (F H m a c j : PTm n) : Γ ⊢[PRAAx] stored (quotient F H m a c j) (succ j) (width a c j) := by
  let S := storedSyntax (quotient (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0))
    (succ (var 0)) (width (Syn.shift a) (Syn.shift c) (var 0))
  have all : Γ ⊢[PRAAx] .all (Foundations.BoundedSyntax.formula S) := by
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,formula_stored,GaussianPolynomialMultiplicationMatrix.subst_stored,subst_quotient,
        GaussianPolynomialMonicHornerReduction.subst_width,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ]
      exact stored_congr (quotient_zero _ _ _ _ _).eqSymm (.eqRefl _) (by unfold width; ipra_ring) (zero_rows_stored _ _)
    · simp only [S,formula_stored,GaussianPolynomialMultiplicationMatrix.subst_stored,subst_quotient,
        GaussianPolynomialMonicHornerReduction.subst_width,Syn.subst_var,Syn.repl_zero,subst_repl_shift,
        ConciseIPRA.PTm.subst_succ]
      exact stored_congr (quotient_succ _ _ _ _ _ _).eqSymm (.eqRefl _) (by unfold width; ipra_ring)
        (inject_stored _ _ _ _ _)
  simpa only [S,formula_stored,GaussianPolynomialMultiplicationMatrix.subst_stored,subst_quotient,
    GaussianPolynomialMonicHornerReduction.subst_width,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] using all.allE j

def qvalue (F H m a c j x y : PTm n) : PTm n := evaluate (values (quotient F H m a c j) (succ j) x) y
def rvalue (F H m a c j x y : PTm n) : PTm n := evaluate (values (stage F H m a c j) m x) y
def leadingValue (F H m a c j x : PTm n) : PTm n := evaluate (entry (stage F H m a c j) zero) x

@[simp] theorem subst_qvalue {k : ℕ} (σ : Fin n → PTm k) (F H m a c j x y : PTm n) :
    Syn.subst σ (qvalue F H m a c j x y) = qvalue (Syn.subst σ F) (Syn.subst σ H)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) (Syn.subst σ x) (Syn.subst σ y) := by simp [qvalue]
@[simp] theorem subst_rvalue {k : ℕ} (σ : Fin n → PTm k) (F H m a c j x y : PTm n) :
    Syn.subst σ (rvalue F H m a c j x y) = rvalue (Syn.subst σ F) (Syn.subst σ H)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) (Syn.subst σ x) (Syn.subst σ y) := by simp [rvalue]

theorem quotient_evaluation_succ (F H m a c j x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qvalue F H m a c (succ j) x y ≐ qadd (qmul (qvalue F H m a c j x y) y) (leadingValue F H m a c j x) := by
  let Q := quotient F H m a c j
  let b := width a c j
  have hQ := Prf.andE₁ (Prf.andE₂ (quotient_stored (Γ := Γ) F H m a c j))
  have main := inject_evaluation (shiftY Q (succ j) b c) (entry (stage F H m a c j) zero) (succ (succ j)) b c x y
    (le_trans (zero_lt_succ j) (le_succ_self _)) (.andE₁ (.andE₂ (shift_stored Q (succ j) b c hQ)))
    (row_shape_at _ _ _ _ (stage_shape _ _ _ _ _ _) hm)
  exact (evaluation_congr (values_congr (quotient_succ _ _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (main.eqTrans (qadd_congr ((shift_evaluation Q (succ j) b c x y).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative _ _)) (.eqRefl _)))

theorem remainder_evaluation_succ (F H m a c j x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hC : Γ ⊢[PRAAx] length (entry H j) ≐ succ a) : Γ ⊢[PRAAx]
    rvalue F H m a c (succ j) x y ≐ qadd
      (evaluate (values (companion F (stage F H m a c j) m (width a c j) c) m x) y) (evaluate (entry H j) x) := by
  let C := companion F (stage F H m a c j) m (width a c j) c
  have shaped : Γ ⊢[PRAAx] stored C m (a+succ j*c) :=
    stored_congr (.eqRefl _) (.eqRefl _) (by unfold width; ipra_ring) (companion_stored _ _ _ _ _)
  exact (evaluation_congr (values_congr (stage_succ _ _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (inject_evaluation C (entry H j) m a (succ j*c) x y hm (.andE₁ (.andE₂ shaped)) hC)

def prefixLaw (F H m a c L x y j : PTm n) : Fm PTm n := le j L ⟶
  horner (values H L x) y j ≐ qadd (qmul (evaluate (monicValues F m x) y) (qvalue F H m a c j x y)) (rvalue F H m a c j x y)

@[simp] theorem subst_prefixLaw {k : ℕ} (σ : Fin n → PTm k) (F H m a c L x y j : PTm n) :
    (prefixLaw F H m a c L x y j).subst σ = prefixLaw (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ j) := by simp [prefixLaw]

theorem reconstruction_succ (F H m a c L x y j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a)
    (hj : Γ ⊢[PRAAx] lt j L) (h : Γ ⊢[PRAAx] prefixLaw F H m a c L x y j) : Γ ⊢[PRAAx]
    horner (values H L x) y (succ j) ≐
      qadd (qmul (evaluate (monicValues F m x) y) (qvalue F H m a c (succ j) x y)) (rvalue F H m a c (succ j) x y) := by
  have step := companion_evaluation F (stage F H m a c j) m (width a c j) c x y hm hF (stage_shape _ _ _ _ _ _)
  have incoming := row_shape_at H L a j hH hj
  exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr (qmul_congr (.impE h (le_of_lt hj)) (.eqRefl y)) (values_lookup _ _ _ _ hj)).eqTrans
      ((GaussianRationalMonicReduction.reconstruction_step _ _ _ _ _ _ _ step).eqTrans
        (qadd_congr (qmul_congr (.eqRefl _) (quotient_evaluation_succ _ _ _ _ _ _ _ _ hm).eqSymm)
          (remainder_evaluation_succ _ _ _ _ _ _ _ _ hm incoming).eqSymm)))

theorem prefix_reconstruction (F H m a c L x y j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    horner (values H L x) y j ≐
      qadd (qmul (evaluate (monicValues F m x) y) (qvalue F H m a c j x y)) (rvalue F H m a c j x y) := by
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  have hFs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hF.shift
  have hHs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (Syn.shift L) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hH.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a)
      (Syn.shift c) (Syn.shift L) (Syn.shift x) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have q0 : Γ ⊢[PRAAx] qvalue F H m a c zero x y ≐ qzero :=
        (evaluation_congr (values_congr (quotient_zero _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
          (zero_rows_evaluation _ _ _ _)
      have r0 : Γ ⊢[PRAAx] rvalue F H m a c zero x y ≐ qzero :=
        (evaluation_congr (values_congr (stage_zero _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
          (zero_rows_evaluation _ _ _ _)
      exact .impI ((GaussianRationalHorner.horner_zero _ _).eqTrans
        ((qadd_congr ((qmul_congr (.eqRefl _) q0).eqTrans (qmul_zero_right _)) r0).eqTrans (qzero_add _ qzero_canonical)).eqSymm).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (reconstruction_succ (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c)
        (Syn.shift L) (Syn.shift x) (Syn.shift y) (var 0) hms.wk.wk hFs.wk.wk hHs.wk.wk Prf.hyp0 Prf.hyp1)
  have atJ : Γ ⊢[PRAAx] prefixLaw F H m a c L x y j := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE atJ hj

theorem original_reconstruction (F H m a c x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H (length H) a) : Γ ⊢[PRAAx]
    evaluate (values H (length H) x) y ≐ qadd (qmul (evaluate (monicValues F m x) y)
      (qvalue F H m a c (length H) x y)) (rvalue F H m a c (length H) x y) :=
  (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    (prefix_reconstruction _ _ _ _ _ _ _ _ _ hm hF hH (le_refl _))

theorem actual_polynomial_horner_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (length (var 1)) (var 3) ⟶
      evaluate (values (var 1) (length (var 1)) (var 5)) (var 6) ≐ qadd
        (qmul (evaluate (monicValues (var 0) (var 2) (var 5)) (var 6))
          (qvalue (var 0) (var 1) (var 2) (var 3) (var 4) (length (var 1)) (var 5) (var 6)))
        (rvalue (var 0) (var 1) (var 2) (var 3) (var 4) (length (var 1)) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (original_reconstruction _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialMonicHornerQuotient
