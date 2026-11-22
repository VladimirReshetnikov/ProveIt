import IPRADerivations.Analysis.GaussianRationalPivotSearch
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Actual column-ordered rectangular elimination and tag history

The real recursor stores a pair of the current matrix and the actual
history. Column c uses the proved least unmarked/nonzero pivot scan;
its zero/succ(row) tag is appended to the stored list. Shape and the
bidirectional homogeneous-system transport are derived by genuine
bounded-syntax/QF induction. No stage, history, rank or null invariant
is a producer input. A rank-profile/free-variable theorem is separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalEliminationLoop

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length empty empty_length append append_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open LeanProofs.IPRA.Analysis.GaussianRationalRowElimination (shape nullRows)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (A R N : PTm n) : PTm n := pairT A (pairT R N)
def advance (E H R N c : PTm n) : PTm n := pairT (GaussianRationalPivotSearch.next E R N H c c)
  (append H (singleton (GaussianRationalPivotSearch.tag E R H c c)))
def baseBody : PTm 1 := pairT (fstT (var 0)) empty
def stepBody : PTm 3 := advance (fstT (var 1)) (sndT (var 1))
  (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0)
def stateF : PR 2 := rec2 baseBody stepBody
def state (A R N c : PTm n) : PTm n := ap2 stateF c (data A R N)
def matrix (A R N c : PTm n) : PTm n := fstT (state A R N c)
def history (A R N c : PTm n) : PTm n := sndT (state A R N c)

@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A R N : PTm n) :
    Syn.subst σ (data A R N) = data (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_advance {k : ℕ} (σ : Fin n → PTm k) (E H R N c : PTm n) :
    Syn.subst σ (advance E H R N c) = advance (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by simp [advance]
@[simp] theorem subst_state {k : ℕ} (σ : Fin n → PTm k) (A R N c : PTm n) :
    Syn.subst σ (state A R N c) = state (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by simp [state]
@[simp] theorem subst_matrix {k : ℕ} (σ : Fin n → PTm k) (A R N c : PTm n) :
    Syn.subst σ (matrix A R N c) = matrix (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by simp [matrix]
@[simp] theorem subst_history {k : ℕ} (σ : Fin n → PTm k) (A R N c : PTm n) :
    Syn.subst σ (history A R N c) = history (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by simp [history]

theorem advance_congr {E E' H H' R R' N N' c c' : PTm n} (hE : Γ ⊢[PRAAx] E ≐ E')
    (hH : Γ ⊢[PRAAx] H ≐ H') (hR : Γ ⊢[PRAAx] R ≐ R') (hN : Γ ⊢[PRAAx] N ≐ N') (hc : Γ ⊢[PRAAx] c ≐ c') : Γ ⊢[PRAAx]
    advance E H R N c ≐ advance E' H' R' N' c' := by
  simpa only [subst_advance,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![E,H,R,N,c]) (σ' := ![E',H',R',N',c'])
      (fun i => by fin_cases i; exact hE; exact hH; exact hR; exact hN; exact hc)
theorem state_zero (A R N : PTm n) : Γ ⊢[PRAAx] state A R N zero ≐ pairT A empty := by
  have e := rec2_zero (Γ := Γ) baseBody stepBody (data A R N)
  simp only [baseBody,subst_pairT,subst_fstT,Foundations.SequenceComposition.subst_empty,Syn.subst_var,Syn.inst_zero] at e
  exact e.eqTrans (congrPairT (fst_pair _ _) (.eqRefl _))
theorem state_succ (A R N c : PTm n) : Γ ⊢[PRAAx] state A R N (succ c) ≐ advance (matrix A R N c) (history A R N c) R N c := by
  have e := rec2_succ (Γ := Γ) baseBody stepBody c (data A R N)
  simp only [stepBody,subst_advance,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  exact e.eqTrans (advance_congr (.eqRefl _) (.eqRefl _)
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _))
theorem matrix_zero (A R N : PTm n) : Γ ⊢[PRAAx] matrix A R N zero ≐ A := (congrFst (state_zero _ _ _)).eqTrans (fst_pair _ _)
theorem history_zero (A R N : PTm n) : Γ ⊢[PRAAx] history A R N zero ≐ empty := (congrSnd (state_zero _ _ _)).eqTrans (snd_pair _ _)
theorem matrix_succ (A R N c : PTm n) : Γ ⊢[PRAAx] matrix A R N (succ c) ≐
    GaussianRationalPivotSearch.next (matrix A R N c) R N (history A R N c) c c :=
  (congrFst (state_succ _ _ _ _)).eqTrans (fst_pair _ _)
theorem history_succ (A R N c : PTm n) : Γ ⊢[PRAAx] history A R N (succ c) ≐
    append (history A R N c) (singleton (GaussianRationalPivotSearch.tag (matrix A R N c) R (history A R N c) c c)) :=
  (congrSnd (state_succ _ _ _ _)).eqTrans (snd_pair _ _)

theorem history_length (A R N c : PTm n) : Γ ⊢[PRAAx] length (history A R N c) ≐ c := by
  have all : Γ ⊢[PRAAx] .all (length (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) ≐ var 0) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_history,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (history_zero _ _ _)).eqTrans empty_length
    · simp only [Fm.subst_eq,subst_length,subst_history,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (history_succ _ _ _ _)).eqTrans ((append_length _ _).eqTrans
        ((congrAdd Prf.hyp0 (singleton_length _)).eqTrans (succ_eq_add_one _).eqSymm))
  simpa only [Fm.subst_eq,subst_length,subst_history,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c

def shapeSyntax (A R N : PTm n) : BFm n := .and (.eq (length A) R)
  (.all R (.eq (length (entry (Syn.shift A) (var 0))) (Syn.shift N)))
theorem shape_formula (A R N : PTm n) : formula (shapeSyntax A R N) = shape A R N := rfl
@[simp] theorem subst_shapeSyntax {k : ℕ} (σ : Fin n → PTm k) (A R N : PTm n) :
    (shapeSyntax A R N).subst σ = shapeSyntax (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [shapeSyntax,Foundations.BoundedSyntax.BFm.subst,Foundations.BoundedFormulas.subst_up_shift']

theorem matrix_shape (A R N c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx] shape (matrix A R N c) R N := by
  let S := shapeSyntax (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) (Syn.shift R) (Syn.shift N)
  have all : Γ ⊢[PRAAx] .all (shape (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) (Syn.shift R) (Syn.shift N)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,shape_formula,GaussianRationalRowElimination.subst_shape,subst_matrix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact GaussianRationalPivotSearch.shape_congr (matrix_zero _ _ _).eqSymm hA
    · simp only [S,shape_formula,GaussianRationalRowElimination.subst_shape,subst_matrix,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact GaussianRationalPivotSearch.shape_congr (matrix_succ _ _ _ _).eqSymm
        (GaussianRationalPivotSearch.next_shape _ _ _ _ _ _ Prf.hyp0)
  simpa only [GaussianRationalRowElimination.subst_shape,subst_matrix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c

theorem history_previous (A R N c j : PTm n) (hj : Γ ⊢[PRAAx] lt j c) : Γ ⊢[PRAAx]
    entry (history A R N (succ c)) j ≐ entry (history A R N c) j :=
  (entry_congr (history_succ _ _ _ _) (.eqRefl _)).eqTrans
    (Foundations.SequenceComposition.append_left (lt_congr (.eqRefl _) (history_length _ _ _ _).eqSymm hj))
theorem append_last (H a : PTm n) : Γ ⊢[PRAAx] entry (append H (singleton a)) (length H) ≐ a :=
  (entry_congr (.eqRefl _) (add_zero (length H)).eqSymm).eqTrans
    ((Foundations.SequenceComposition.append_right (a := H) (b := singleton a) (i := zero)
      (lt_congr (.eqRefl _) (singleton_length a).eqSymm (zero_lt_succ zero))).eqTrans (singleton_lookup _))
theorem history_tag (A R N c : PTm n) : Γ ⊢[PRAAx] entry (history A R N (succ c)) c ≐
    GaussianRationalPivotSearch.tag (matrix A R N c) R (history A R N c) c c :=
  (entry_congr (history_succ _ _ _ _) (history_length _ _ _ _).eqSymm).eqTrans (append_last _ _)
theorem history_skip (A R N c : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRationalPivotSearch.flag (matrix A R N c) R (history A R N c) c c ≐ zero) : Γ ⊢[PRAAx]
    entry (history A R N (succ c)) c ≐ zero := (history_tag _ _ _ _).eqTrans (GaussianRationalPivotSearch.tag_failure _ _ _ _ _ hf)
theorem history_pivot (A R N c : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRationalPivotSearch.flag (matrix A R N c) R (history A R N c) c c ≐ one) : Γ ⊢[PRAAx]
    entry (history A R N (succ c)) c ≐ succ (GaussianRationalPivotSearch.selected (matrix A R N c) R (history A R N c) c c) :=
  (history_tag _ _ _ _).eqTrans (GaussianRationalPivotSearch.tag_success _ _ _ _ _ hf)

def nullSyntax (E R N l : PTm n) : BFm n := .all R
  (.eq (GaussianRationalRowElimination.rowDot (Syn.shift E) (Syn.shift N) (Syn.shift l) (var 0)) GaussianRationalHorner.qzero)
theorem null_formula (E R N l : PTm n) : formula (nullSyntax E R N l) = nullRows E R N l := rfl
def nullLaw (A R N l c : PTm n) : Fm PTm n := le c N ⟶
  Fm.iff (nullRows A R N l) (nullRows (matrix A R N c) R N l)
def nullLawSyntax (A R N l c : PTm n) : BFm n := .imp (.le c N)
  (.and (.imp (nullSyntax A R N l) (nullSyntax (matrix A R N c) R N l))
    (.imp (nullSyntax (matrix A R N c) R N l) (nullSyntax A R N l)))
theorem null_law_formula (A R N l c : PTm n) : formula (nullLawSyntax A R N l c) = nullLaw A R N l c := rfl
@[simp] theorem subst_nullLaw {k : ℕ} (σ : Fin n → PTm k) (A R N l c : PTm n) :
    (nullLaw A R N l c).subst σ = nullLaw (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ l) (Syn.subst σ c) := by
  simp [nullLaw,Fm.iff]

theorem prefix_null_equivalence (A R N l c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hc : Γ ⊢[PRAAx] le c N) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (matrix A R N c) R N l) := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_shape,Syn.shift] using hA.shift
  let S := nullLawSyntax (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift l) (var 0)
  have all : Γ ⊢[PRAAx] .all (nullLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift l) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,null_law_formula,subst_nullLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI (.andI (.impI ?_) (.impI ?_))
      · exact GaussianRationalRowElimination.null_rows_congr (matrix_zero _ _ _).eqSymm Prf.hyp0
      · exact GaussianRationalRowElimination.null_rows_congr (matrix_zero _ _ _) Prf.hyp0
    · simp only [S,null_law_formula,subst_nullLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) :: nullLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift l) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] Fm.iff (nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift l))
          (nullRows (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) (Syn.shift R) (Syn.shift N) (Syn.shift l)) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have localStep := GaussianRationalPivotSearch.next_null_equivalence (Γ := Δ)
        (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) (Syn.shift R) (Syn.shift N)
        (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) (var 0) (var 0) (Syn.shift l)
        (matrix_shape _ _ _ _ hAs.wk.wk) Prf.hyp0
      exact .andI (.impI (GaussianRationalRowElimination.null_rows_congr (matrix_succ _ _ _ _).eqSymm
        (localStep.wk.iffMp (ih.wk.iffMp Prf.hyp0))))
        (.impI (ih.wk.iffMpr (localStep.wk.iffMpr
          (GaussianRationalRowElimination.null_rows_congr (matrix_succ _ _ _ _) Prf.hyp0))))
  have queried : Γ ⊢[PRAAx] nullLaw A R N l c := by
    simpa only [subst_nullLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c
  exact .impE queried hc

theorem final_null_equivalence (A R N l : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (matrix A R N N) R N l) := prefix_null_equivalence _ _ _ _ _ hA (le_refl _)

/-! The actual PR4 retains the queried numerical prefix as a returned field. -/
def output (A R N c : PTm n) : PTm n := pairT (matrix A R N c) (pairT (history A R N c) c)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (A R N c : PTm n) : PTm n := app outputF ![A,R,N,c]
def fields (p : PTm n) : Fin 3 → PTm n := ![fstT p,fstT (sndT p),sndT (sndT p)]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (A R N c : PTm n) :
    Syn.subst σ (output A R N c) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R N c : PTm n) :
    Syn.subst σ (run A R N c) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) (i : Fin 3) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (A R N c : PTm n) : Γ ⊢[PRAAx] run A R N c ≐ output A R N c := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,R,N,c]
theorem returned_fields (A R N c : PTm n) (i : Fin 3) : Γ ⊢[PRAAx]
    fields (run A R N c) i ≐ ![matrix A R N c,history A R N c,c] i := by
  have e0 := program_at (Γ := Γ) A R N c
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrSnd e1).eqTrans (snd_pair _ _)
theorem returned_history_length (A R N c : PTm n) : Γ ⊢[PRAAx]
    length (fields (run A R N c) 1) ≐ fields (run A R N c) 2 :=
  (congrFst (returned_fields _ _ _ _ 1)).eqTrans ((history_length _ _ _ _).eqTrans (returned_fields _ _ _ _ 2).eqSymm)
theorem returned_shape (A R N c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    shape (fields (run A R N c) 0) R N := GaussianRationalPivotSearch.shape_congr
      (returned_fields _ _ _ _ 0).eqSymm (matrix_shape _ _ _ _ hA)
theorem returned_null_equivalence (A R N c l : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hc : Γ ⊢[PRAAx] le c N) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (fields (run A R N c) 0) R N l) := by
  have actual := prefix_null_equivalence A R N l c hA hc
  exact .andI (.impI (GaussianRationalRowElimination.null_rows_congr (returned_fields _ _ _ _ 0).wk.eqSymm (actual.wk.iffMp Prf.hyp0)))
    (.impI (actual.wk.iffMpr (GaussianRationalRowElimination.null_rows_congr (returned_fields _ _ _ _ 0).wk Prf.hyp0)))

theorem actual_base_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (state (var 0) (var 1) (var 2) zero ≐ pairT (var 0) empty) := closeUniv 3 (state_zero _ _ _)
theorem actual_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (state (var 0) (var 1) (var 2) (succ (var 3)) ≐
      advance (matrix (var 0) (var 1) (var 2) (var 3)) (history (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (state_succ _ _ _ _)
theorem actual_history_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (history (var 0) (var 1) (var 2) (var 3)) ≐ var 3) := closeUniv 4 (history_length _ _ _ _)
theorem actual_history_previous_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 3) ⟶ entry (history (var 0) (var 1) (var 2) (succ (var 3))) (var 4) ≐
      entry (history (var 0) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (history_previous _ _ _ _ _ Prf.hyp0))
theorem actual_history_tag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (history (var 0) (var 1) (var 2) (succ (var 3))) (var 3) ≐
      GaussianRationalPivotSearch.tag (matrix (var 0) (var 1) (var 2) (var 3)) (var 1)
        (history (var 0) (var 1) (var 2) (var 3)) (var 3) (var 3)) := closeUniv 4 (history_tag _ _ _ _)
theorem actual_history_skip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalPivotSearch.flag (matrix (var 0) (var 1) (var 2) (var 3)) (var 1)
      (history (var 0) (var 1) (var 2) (var 3)) (var 3) (var 3) ≐ zero ⟶
        entry (history (var 0) (var 1) (var 2) (succ (var 3))) (var 3) ≐ zero) := closeUniv 4 (.impI (history_skip _ _ _ _ Prf.hyp0))
theorem actual_history_pivot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalPivotSearch.flag (matrix (var 0) (var 1) (var 2) (var 3)) (var 1)
      (history (var 0) (var 1) (var 2) (var 3)) (var 3) (var 3) ≐ one ⟶
        entry (history (var 0) (var 1) (var 2) (succ (var 3))) (var 3) ≐
          succ (GaussianRationalPivotSearch.selected (matrix (var 0) (var 1) (var 2) (var 3)) (var 1)
            (history (var 0) (var 1) (var 2) (var 3)) (var 3) (var 3))) := closeUniv 4 (.impI (history_pivot _ _ _ _ Prf.hyp0))
theorem actual_rectangular_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ shape (matrix (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2)) :=
  closeUniv 4 (.impI (matrix_shape _ _ _ _ Prf.hyp0))
theorem actual_prefix_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶
      Fm.iff (nullRows (var 0) (var 1) (var 2) (var 4))
        (nullRows (matrix (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (prefix_null_equivalence _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_final_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ Fm.iff (nullRows (var 0) (var 1) (var 2) (var 3))
      (nullRows (matrix (var 0) (var 1) (var 2) (var 2)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (final_null_equivalence _ _ _ _ Prf.hyp0))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_history_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (fields (run (var 0) (var 1) (var 2) (var 3)) 1) ≐ fields (run (var 0) (var 1) (var 2) (var 3)) 2) :=
  closeUniv 4 (returned_history_length _ _ _ _)
theorem actual_returned_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶ Fm.iff (nullRows (var 0) (var 1) (var 2) (var 4))
      (nullRows (fields (run (var 0) (var 1) (var 2) (var 3)) 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_null_equivalence _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalEliminationLoop
