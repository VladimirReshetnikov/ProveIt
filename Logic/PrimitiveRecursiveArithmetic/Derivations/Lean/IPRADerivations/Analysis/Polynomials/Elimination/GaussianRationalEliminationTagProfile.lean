import IPRADerivations.Analysis.Polynomials.Elimination.GaussianRationalEliminationLoop

/-!
# Actual bounded and injective elimination tags

The actual history is read from the original column loop. Every nonzero
tag names a bounded row, and no nonzero row tag occurs twice. The proofs
use genuine QF induction at independent numerical queried columns; the
bounded universal statements follow afterwards. The actual row-column
lookup reuses the SAME different-tag search body as pivot availability.
No shape, rank, valid history, cell profile or lookup law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalEliminationTagProfile

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalEliminationLoop (matrix history history_length history_previous history_tag history_skip history_pivot)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem last_tag_bound (A R N c : PTm n) : Γ ⊢[PRAAx] le (entry (history A R N (succ c)) c) R := by
  refine .orE (GaussianRationalPivotSearch.flag_cases (matrix A R N c) R (history A R N c) c c) ?_ ?_
  · exact le_congr (history_skip _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (zero_le R)
  · exact le_congr (history_pivot _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _)
      (.andE₁ (GaussianRationalPivotSearch.selected_correct _ _ _ _ _ Prf.hyp0))

def boundLaw (A R N j c : PTm n) : Fm PTm n := lt j c ⟶ le (entry (history A R N c) j) R
@[simp] theorem subst_boundLaw {k : ℕ} (σ : Fin n → PTm k) (A R N j c : PTm n) :
    (boundLaw A R N j c).subst σ = boundLaw (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ j) (Syn.subst σ c) := by simp [boundLaw]
theorem bound_step (A R N j c : PTm n) (hOld : Γ ⊢[PRAAx] boundLaw A R N j c) : Γ ⊢[PRAAx] boundLaw A R N j (succ c) := by
  refine .impI (.orE (lt_succ_cases Prf.hyp0) ?_ ?_)
  · exact le_congr (history_previous _ _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (.impE hOld.wk.wk Prf.hyp0)
  · exact le_congr (entry_congr (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _) (last_tag_bound _ _ _ _)
theorem tag_bound (A R N c j : PTm n) (hj : Γ ⊢[PRAAx] lt j c) : Γ ⊢[PRAAx] le (entry (history A R N c) j) R := by
  have all : Γ ⊢[PRAAx] .all (boundLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift j) (var 0)) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [subst_boundLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact bound_step _ _ _ _ _ Prf.hyp0
  have queried : Γ ⊢[PRAAx] boundLaw A R N j c := by
    simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c
  exact .impE queried hj

theorem fresh_tag (A R N c j : PTm n) (hj : Γ ⊢[PRAAx] lt j c)
    (hNZ : Γ ⊢[PRAAx] neg (entry (history A R N (succ c)) c ≐ zero)) : Γ ⊢[PRAAx]
    neg (entry (history A R N c) j ≐ entry (history A R N (succ c)) c) := by
  refine .orE (GaussianRationalPivotSearch.flag_cases (matrix A R N c) R (history A R N c) c c) ?_ ?_
  · exact .botE _ (.impE hNZ.wk (history_skip _ _ _ _ Prf.hyp0))
  · have success := GaussianRationalPivotSearch.selected_correct (Γ := (GaussianRationalPivotSearch.flag (matrix A R N c) R (history A R N c) c c ≐ one) :: Γ)
      (matrix A R N c) R (history A R N c) c c Prf.hyp0
    have unmarked := GaussianRationalPivotSearch.unmarked_at _ _ _ _ (.andE₁ (.andE₂ success)) hj.wk
    exact .impI (.impE unmarked.wk (Prf.hyp0.eqTrans (history_pivot _ _ _ _ Prf.hyp1)))

def distinctLaw (A R N j k c : PTm n) : Fm PTm n := lt j k ⟶ lt k c ⟶
  neg (entry (history A R N c) k ≐ zero) ⟶ neg (entry (history A R N c) j ≐ entry (history A R N c) k)
@[simp] theorem subst_distinctLaw {l : ℕ} (σ : Fin n → PTm l) (A R N j k c : PTm n) :
    (distinctLaw A R N j k c).subst σ = distinctLaw (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ c) := by simp [distinctLaw]

theorem distinct_step (A R N j k c : PTm n) (hOld : Γ ⊢[PRAAx] distinctLaw A R N j k c) : Γ ⊢[PRAAx] distinctLaw A R N j k (succ c) := by
  refine .impI (.impI (.impI ?_))
  let Δ := neg (entry (history A R N (succ c)) k ≐ zero) :: lt k (succ c) :: lt j k :: Γ
  have hjk : Δ ⊢[PRAAx] lt j k := .hyp (by simp [Δ])
  have hkc : Δ ⊢[PRAAx] lt k (succ c) := Prf.hyp1
  have hnz : Δ ⊢[PRAAx] neg (entry (history A R N (succ c)) k ≐ zero) := Prf.hyp0
  refine .orE (lt_succ_cases hkc) ?_ ?_
  · have ej := history_previous (Γ := lt k c :: Δ) A R N c j (lt_of_lt_of_le hjk.wk (le_of_lt Prf.hyp0))
    have ek := history_previous (Γ := lt k c :: Δ) A R N c k Prf.hyp0
    have oldNZ : (lt k c) :: Δ ⊢[PRAAx] neg (entry (history A R N c) k ≐ zero) :=
      .impI (.impE hnz.wk.wk (ek.wk.eqTrans Prf.hyp0))
    have oldNe : (lt k c) :: Δ ⊢[PRAAx] neg (entry (history A R N c) j ≐ entry (history A R N c) k) :=
      .impE (.impE (.impE hOld.wk.wk.wk.wk hjk.wk) Prf.hyp0) oldNZ
    exact .impI (.impE oldNe.wk (ej.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans ek.wk)))
  · have hjc : (k ≐ c) :: Δ ⊢[PRAAx] lt j c := lt_congr (.eqRefl _) Prf.hyp0 hjk.wk
    have ek : (k ≐ c) :: Δ ⊢[PRAAx] entry (history A R N (succ c)) k ≐ entry (history A R N (succ c)) c := entry_congr (.eqRefl _) Prf.hyp0
    have newNZ : (k ≐ c) :: Δ ⊢[PRAAx] neg (entry (history A R N (succ c)) c ≐ zero) :=
      .impI (.impE hnz.wk.wk (ek.wk.eqTrans Prf.hyp0))
    have fresh := fresh_tag A R N c j hjc newNZ
    have ej := history_previous A R N c j hjc
    exact .impI (.impE fresh.wk (ej.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans ek.wk)))

theorem earlier_distinct (A R N c j k : PTm n) (hjk : Γ ⊢[PRAAx] lt j k) (hkc : Γ ⊢[PRAAx] lt k c)
    (hNZ : Γ ⊢[PRAAx] neg (entry (history A R N c) k ≐ zero)) : Γ ⊢[PRAAx]
    neg (entry (history A R N c) j ≐ entry (history A R N c) k) := by
  have all : Γ ⊢[PRAAx] .all (distinctLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift j) (Syn.shift k) (var 0)) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,lt_QF _ _,⟨trivial,trivial⟩,trivial,trivial⟩ ?_ ?_
    · simp only [subst_distinctLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (.impI (lt_zero_absurd _ Prf.hyp0))
    · simp only [subst_distinctLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact distinct_step _ _ _ _ _ _ Prf.hyp0
  have queried : Γ ⊢[PRAAx] distinctLaw A R N j k c := by
    simpa only [subst_distinctLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c
  exact .impE (.impE (.impE queried hjk) hkc) hNZ

theorem equal_tags_unique (A R N c j k : PTm n) (hj : Γ ⊢[PRAAx] lt j c) (hk : Γ ⊢[PRAAx] lt k c)
    (hNZ : Γ ⊢[PRAAx] neg (entry (history A R N c) j ≐ zero))
    (he : Γ ⊢[PRAAx] entry (history A R N c) j ≐ entry (history A R N c) k) : Γ ⊢[PRAAx] j ≐ k := by
  have knz : Γ ⊢[PRAAx] neg (entry (history A R N c) k ≐ zero) := .impI (.impE hNZ.wk (he.wk.eqTrans Prf.hyp0))
  refine .orE (lt_or_le j k) ?_ ?_
  · exact .botE _ (.impE (earlier_distinct _ _ _ _ _ _ Prf.hyp0 hk.wk knz.wk) he.wk)
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ Prf.hyp0.eqSymm
    exact .botE _ (.impE (earlier_distinct _ _ _ _ _ _ Prf.hyp0 hj.wk.wk hNZ.wk.wk) he.wk.wk.eqSymm)

def validTags (H R c : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift c) ⟶ le (entry (Syn.shift H) (var 0)) (Syn.shift R))
def injectiveTags (H c : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift c) ⟶ .all
  (lt (var 0) (var 1) ⟶ neg (entry (Syn.shift (Syn.shift H)) (var 1) ≐ zero) ⟶
    neg (entry (Syn.shift (Syn.shift H)) (var 0) ≐ entry (Syn.shift (Syn.shift H)) (var 1))))
@[simp] theorem subst_validTags {k : ℕ} (σ : Fin n → PTm k) (H R c : PTm n) :
    (validTags H R c).subst σ = validTags (Syn.subst σ H) (Syn.subst σ R) (Syn.subst σ c) := by
  simp [validTags,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_injectiveTags {k : ℕ} (σ : Fin n → PTm k) (H c : PTm n) :
    (injectiveTags H c).subst σ = injectiveTags (Syn.subst σ H) (Syn.subst σ c) := by
  simp [injectiveTags,Syn.subst_shift,Syn.shift_subst]
theorem valid_history (A R N c : PTm n) : Γ ⊢[PRAAx] validTags (history A R N c) R c := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianRationalEliminationLoop.subst_history] using
    tag_bound (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c) (var 0) Prf.hyp0
theorem injective_history (A R N c : PTm n) : Γ ⊢[PRAAx] injectiveTags (history A R N c) c := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let Δ := neg (entry (Syn.shift (Syn.shift (history A R N c))) (var 1) ≐ zero) :: lt (var 0) (var 1) ::
    (lt (var 0) (Syn.shift c)).shift :: (Γ.map Fm.shift).map Fm.shift
  have rawRange : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift c)).shift := .hyp (by simp [Δ])
  have range : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift c)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using rawRange
  have nz : Δ ⊢[PRAAx] neg (entry (history (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift c))) (var 1) ≐ zero) := by
    simpa only [Δ,List.map_cons,Syn.shift,GaussianRationalEliminationLoop.subst_history,Fm.shift,subst_lt,Syn.subst_var,Fin.succ_zero_eq_one] using
      (Prf.hyp0 : Δ ⊢[PRAAx] neg (entry (Syn.shift (Syn.shift (history A R N c))) (var 1) ≐ zero))
  simpa only [Δ,List.map_cons,Syn.shift,GaussianRationalEliminationLoop.subst_history,Fm.shift,subst_lt,Syn.subst_var,Fin.succ_zero_eq_one] using
    earlier_distinct (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift N))
      (Syn.shift (Syn.shift c)) (var 0) (var 1) Prf.hyp1 range nz

/-! This is precisely the existing availability counterexample search,
not a second selector or an externally supplied inverse map. -/
def column (H c r : PTm n) : PTm n := Search.mu GaussianRationalPivotSearch.differentBody c (GaussianRationalPivotSearch.markData H r)
def rowColumn (A R N c r : PTm n) : PTm n := column (history A R N c) c r
@[simp] theorem subst_column {k : ℕ} (σ : Fin n → PTm k) (H c r : PTm n) :
    Syn.subst σ (column H c r) = column (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ r) := by simp [column,Search.mu]
@[simp] theorem subst_rowColumn {k : ℕ} (σ : Fin n → PTm k) (A R N c r : PTm n) :
    Syn.subst σ (rowColumn A R N c r) = rowColumn (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ r) := by simp [rowColumn]
theorem column_bound (H c r : PTm n) : Γ ⊢[PRAAx] le (column H c r) c :=
  .andE₁ (Search.search_spec (f := GaussianRationalPivotSearch.differentBody) c zero (GaussianRationalPivotSearch.markData H r))
theorem column_found (H c r : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalPivotSearch.available H c r ≐ zero) : Γ ⊢[PRAAx]
    lt (column H c r) c ⋏ entry H (column H c r) ≐ succ r := by
  have found := Foundations.BoundedReflection.all_fail GaussianRationalPivotSearch.differentBody h
  have hit : Γ ⊢[PRAAx] PTm.monus one (eqb (entry H (column H c r)) (succ r)) ≐ zero :=
    (GaussianRationalPivotSearch.different_body_at H r (column H c r)).eqSymm.eqTrans (.andE₂ found)
  exact .andI (.andE₁ found) (AnalyticNumberTheory.Valuation.eq_of_eqb_ne (Foundations.BoundedReflection.ne_of_compl hit))
theorem column_default (H c r : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalPivotSearch.unmarked H c r) : Γ ⊢[PRAAx]
    column H c r ≐ c :=
  Foundations.BoundedReflection.eq_of_eqb ((Foundations.BoundedReflection.all_eq_search GaussianRationalPivotSearch.differentBody c
    (GaussianRationalPivotSearch.markData H r)).eqSymm.eqTrans (GaussianRationalPivotSearch.unmarked_available H c r h))
theorem column_witness (H c r j : PTm n) (hj : Γ ⊢[PRAAx] lt j c) (he : Γ ⊢[PRAAx] entry H j ≐ succ r) : Γ ⊢[PRAAx]
    lt (column H c r) c ⋏ entry H (column H c r) ≐ succ r := by
  have hit := (GaussianRationalPivotSearch.different_body_at (Γ := Γ) H r j).eqTrans
    ((congrMonus (.eqRefl _) (eqb_of_eq he)).eqTrans (monus_self one))
  have found := Search.search_found (f := GaussianRationalPivotSearch.differentBody) hit hj
  have actual : Γ ⊢[PRAAx] PTm.monus one (eqb (entry H (column H c r)) (succ r)) ≐ zero :=
    (GaussianRationalPivotSearch.different_body_at H r (column H c r)).eqSymm.eqTrans (.andE₁ (.andE₂ found))
  exact .andI (.andE₁ found) (AnalyticNumberTheory.Valuation.eq_of_eqb_ne (Foundations.BoundedReflection.ne_of_compl actual))
theorem row_column_bound (A R N c r : PTm n) : Γ ⊢[PRAAx] le (rowColumn A R N c r) c := column_bound _ _ _
theorem row_column_found (A R N c r : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalPivotSearch.available (history A R N c) c r ≐ zero) : Γ ⊢[PRAAx]
    lt (rowColumn A R N c r) c ⋏ ((entry (history A R N c) (rowColumn A R N c r) ≐ succ r) ⋏ lt r R) := by
  have found := column_found _ _ _ h
  have bounded := tag_bound A R N c (rowColumn A R N c r) (.andE₁ found)
  exact .andI (.andE₁ found) (.andI (.andE₂ found) (le_congr (.andE₂ found) (.eqRefl _) bounded))
theorem row_column_at (A R N c r j : PTm n) (hj : Γ ⊢[PRAAx] lt j c)
    (he : Γ ⊢[PRAAx] entry (history A R N c) j ≐ succ r) : Γ ⊢[PRAAx] rowColumn A R N c r ≐ j := by
  have found := column_witness (history A R N c) c r j hj he
  have nonzero : Γ ⊢[PRAAx] neg (entry (history A R N c) (rowColumn A R N c r) ≐ zero) :=
    .impI (succ_ne_zero ((Prf.andE₂ found).wk.eqSymm.eqTrans Prf.hyp0))
  exact equal_tags_unique A R N c (rowColumn A R N c r) j (.andE₁ found) hj nonzero ((Prf.andE₂ found).eqTrans he.eqSymm)

def output (A R N c r : PTm n) : PTm n := pairT (rowColumn A R N c r)
  (pairT (history A R N c) (pairT (entry (history A R N c) (rowColumn A R N c r)) c))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R N c r : PTm n) : PTm n := app outputF ![A,R,N,c,r]
def fields (p : PTm n) : Fin 4 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (A R N c r : PTm n) :
    Syn.subst σ (output A R N c r) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ r) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R N c r : PTm n) :
    Syn.subst σ (run A R N c r) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ r) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (A R N c r : PTm n) : Γ ⊢[PRAAx] run A R N c r ≐ output A R N c r := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,N,c,r]
theorem returned_fields (A R N c r : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    fields (run A R N c r) i ≐ ![rowColumn A R N c r,history A R N c,entry (history A R N c) (rowColumn A R N c r),c] i := by
  have e0 := program_at (Γ := Γ) A R N c r
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem returned_bound (A R N c r : PTm n) : Γ ⊢[PRAAx]
    le (fields (run A R N c r) 0) (fields (run A R N c r) 3) :=
  le_congr (returned_fields _ _ _ _ _ 0).eqSymm (returned_fields _ _ _ _ _ 3).eqSymm (row_column_bound _ _ _ _ _)
theorem returned_column_at (A R N c r j : PTm n) (hj : Γ ⊢[PRAAx] lt j c)
    (he : Γ ⊢[PRAAx] entry (history A R N c) j ≐ succ r) : Γ ⊢[PRAAx] fields (run A R N c r) 0 ≐ j :=
  (returned_fields _ _ _ _ _ 0).eqTrans (row_column_at _ _ _ _ _ _ hj he)

theorem actual_tag_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 3) ⟶ le (entry (history (var 0) (var 1) (var 2) (var 3)) (var 4)) (var 1)) :=
  closeUniv 5 (.impI (tag_bound _ _ _ _ _ Prf.hyp0))
theorem actual_fresh_tag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 3) ⟶ neg (entry (history (var 0) (var 1) (var 2) (succ (var 3))) (var 3) ≐ zero) ⟶
      neg (entry (history (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        entry (history (var 0) (var 1) (var 2) (succ (var 3))) (var 3))) :=
  closeUniv 5 (.impI (.impI (fresh_tag _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_earlier_distinct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 5) ⟶ lt (var 5) (var 3) ⟶
      neg (entry (history (var 0) (var 1) (var 2) (var 3)) (var 5) ≐ zero) ⟶
        neg (entry (history (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
          entry (history (var 0) (var 1) (var 2) (var 3)) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (earlier_distinct _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_valid_history_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (validTags (history (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3)) := closeUniv 4 (valid_history _ _ _ _)
theorem actual_injective_history_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (injectiveTags (history (var 0) (var 1) (var 2) (var 3)) (var 3)) := closeUniv 4 (injective_history _ _ _ _)
theorem actual_equal_tags_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 3) ⟶ lt (var 5) (var 3) ⟶
      neg (entry (history (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ zero) ⟶
        entry (history (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ entry (history (var 0) (var 1) (var 2) (var 3)) (var 5) ⟶
          var 4 ≐ var 5) := closeUniv 6 (.impI (.impI (.impI (.impI
    (equal_tags_unique _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_row_column_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (rowColumn (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3)) := closeUniv 5 (row_column_bound _ _ _ _ _)
theorem actual_row_column_found_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalPivotSearch.available (history (var 0) (var 1) (var 2) (var 3)) (var 3) (var 4) ≐ zero ⟶
      (lt (rowColumn (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) ⋏
        ((entry (history (var 0) (var 1) (var 2) (var 3)) (rowColumn (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ succ (var 4)) ⋏ lt (var 4) (var 1)))) :=
  closeUniv 5 (.impI (row_column_found _ _ _ _ _ Prf.hyp0))
theorem actual_row_column_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 3) ⟶ entry (history (var 0) (var 1) (var 2) (var 3)) (var 5) ≐ succ (var 4) ⟶
      rowColumn (var 0) (var 1) (var 2) (var 3) (var 4) ≐ var 5) := closeUniv 6 (.impI (.impI (row_column_at _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_unmarked_column_default_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalPivotSearch.unmarked (history (var 0) (var 1) (var 2) (var 3)) (var 3) (var 4) ⟶
      rowColumn (var 0) (var 1) (var 2) (var 3) (var 4) ≐ var 3) := closeUniv 5 (.impI (column_default _ _ _ Prf.hyp0))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 0) (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 3)) :=
  closeUniv 5 (returned_bound _ _ _ _ _)
theorem actual_returned_column_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 3) ⟶ entry (history (var 0) (var 1) (var 2) (var 3)) (var 5) ≐ succ (var 4) ⟶
      fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 0 ≐ var 5) := closeUniv 6 (.impI (.impI (returned_column_at _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalEliminationTagProfile
