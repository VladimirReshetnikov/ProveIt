import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationLoop
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationZeroColumn

/-!
# Zero entries in unmarked rows of the elimination prefix

At each computed prefix, an unmarked row has field value zero in
every processed column. The proof treats the new column by the actual
pivot scan and keeps earlier columns by the selected row's zero values.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalEliminationUnmarkedRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalRowElimination (pivot shape)
open GaussianRationalEliminationLoop (matrix history matrix_succ matrix_shape history_previous history_pivot)
open GaussianRationalPivotSearch (unmarked unmarked_at flag flag_cases selected selected_correct next next_failure
  failed_unmarked_zero next_pivot_zero)
open GaussianTranslatedNonconstant (recode_congr recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroRows (E H R c : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift R) ⟶ unmarked (Syn.shift H) (Syn.shift c) (var 0) ⟶ .all
    (lt (var 0) (Syn.shift (Syn.shift c)) ⟶
      pivot (Syn.shift (Syn.shift E)) (Syn.shift (var 0)) (var 0) ≐ qzero))

def unmarkedSyntax (H c r : PTm n) : BFm n := .all c
  (.not (.eq (entry (Syn.shift H) (var 0)) (succ (Syn.shift r))))

def zeroRowsSyntax (E H R c : PTm n) : BFm n := .all R
  (.imp (unmarkedSyntax (Syn.shift H) (Syn.shift c) (var 0))
    (.all (Syn.shift c) (.eq
      (pivot (Syn.shift (Syn.shift E)) (Syn.shift (var 0)) (var 0)) qzero)))

theorem zero_rows_formula (E H R c : PTm n) : formula (zeroRowsSyntax E H R c) = zeroRows E H R c := rfl

@[simp] theorem subst_zeroRows {k : ℕ} (σ : Fin n → PTm k) (E H R c : PTm n) :
    (zeroRows E H R c).subst σ = zeroRows (Syn.subst σ E) (Syn.subst σ H) (Syn.subst σ R) (Syn.subst σ c) := by
  simp [zeroRows,Syn.subst_shift,Syn.shift_subst]

theorem row_zero_at (E H R c r j : PTm n) (h : Γ ⊢[PRAAx] zeroRows E H R c) (hr : Γ ⊢[PRAAx] lt r R)
    (hu : Γ ⊢[PRAAx] unmarked H c r) (hj : Γ ⊢[PRAAx] lt j c) : Γ ⊢[PRAAx] pivot E r j ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt r R ⟶ unmarked H c r ⟶
      .all (lt (var 0) (Syn.shift c) ⟶ pivot (Syn.shift E) (Syn.shift r) (var 0) ≐ qzero) := by
    simpa only [zeroRows,Fm.subst_imp,Fm.subst_all,Fm.subst_eq,subst_lt,
      GaussianRationalPivotSearch.subst_unmarked,GaussianRationalRowElimination.subst_pivot,
      GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,Syn.up_zero,
      Foundations.BoundedFormulas.subst_up_shift'] using h.allE r
  have all := Prf.impE (Prf.impE rule hr) hu
  have atJ : Γ ⊢[PRAAx] lt j c ⟶ pivot E r j ≐ qzero := by simpa using all.allE j
  exact .impE atJ hj

theorem unmarked_before (A R N c r : PTm n) (h : Γ ⊢[PRAAx] unmarked (history A R N (succ c)) (succ c) r) :
    Γ ⊢[PRAAx] unmarked (history A R N c) c r := by
  refine .allI (.impI (.impI ?_))
  have old : Γ.map Fm.shift ⊢[PRAAx] unmarked
      (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (succ (Syn.shift c))) (succ (Syn.shift c)) (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  let Δ := (entry (Syn.shift (history A R N c)) (var 0) ≐ succ (Syn.shift r)) ::
    lt (var 0) (Syn.shift c) :: Γ.map Fm.shift
  have prev := history_previous (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c) (var 0) Prf.hyp1
  have tag : Δ ⊢[PRAAx] entry (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c)) (var 0) ≐
      succ (Syn.shift r) := by simpa [Δ,Syn.shift] using (Prf.hyp0 (Γ := lt (var 0) (Syn.shift c) :: Γ.map Fm.shift))
  exact .impE (unmarked_at _ _ _ _ old.wk.wk (le_trans Prf.hyp1 (le_succ_self _))) (prev.eqTrans tag)

theorem pivot_congr_matrix {E E' : PTm n} (h : Γ ⊢[PRAAx] E ≐ E') (r j : PTm n) :
    Γ ⊢[PRAAx] pivot E r j ≐ pivot E' r j :=
  recode_congr (entry_congr (entry_congr h (.eqRefl r)) (.eqRefl j))

theorem advanced_zero_at (A R N c r j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] lt c N) (hr : Γ ⊢[PRAAx] lt r R)
    (hu : Γ ⊢[PRAAx] unmarked (history A R N (succ c)) (succ c) r) (hj : Γ ⊢[PRAAx] lt j (succ c))
    (h : Γ ⊢[PRAAx] zeroRows (matrix A R N c) (history A R N c) R c) :
    Γ ⊢[PRAAx] pivot (matrix A R N (succ c)) r j ≐ qzero := by
  let E := matrix A R N c
  let H := history A R N c
  let C := next E R N H c c
  have same := matrix_succ (Γ := Γ) A R N c
  have old := unmarked_before A R N c r hu
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hj)) ?_ ?_
  · have seed : (lt j c) :: Γ ⊢[PRAAx] flag E R H c c ≐ one ⟶ pivot E (selected E R H c c) j ≐ qzero := by
      refine .impI ?_
      have selectedFacts := selected_correct (Γ := (flag E R H c c ≐ one) :: lt j c :: Γ) E R H c c Prf.hyp0
      exact row_zero_at E H R c (selected E R H c c) j h.wk.wk (.andE₁ selectedFacts)
        (.andE₁ (.andE₂ selectedFacts)) Prf.hyp1
    exact (pivot_congr_matrix same.wk r j).eqTrans
      ((GaussianRationalEliminationZeroColumn.next_preserves_column E R N H c c r j hr.wk
        (le_trans Prf.hyp0 (le_trans (le_succ_self c) hc.wk)) seed).eqTrans
        (row_zero_at E H R c r j h.wk hr.wk old.wk Prf.hyp0))
  · have column : (j ≐ c) :: Γ ⊢[PRAAx] pivot C r c ≐ qzero := by
      refine .orE (flag_cases E R H c c) ?_ ?_
      · exact (pivot_congr_matrix (next_failure E R N H c c Prf.hyp0) r c).eqTrans
          (failed_unmarked_zero E R H c c r Prf.hyp0 hr.wk.wk old.wk.wk)
      · have selectedTag := history_pivot (Γ := (flag E R H c c ≐ one) :: (j ≐ c) :: Γ) A R N c Prf.hyp0
        have notTag := unmarked_at (Γ := (flag E R H c c ≐ one) :: (j ≐ c) :: Γ)
          (history A R N (succ c)) (succ c) r c hu.wk.wk (le_refl (succ c))
        have different : (flag E R H c c ≐ one) :: (j ≐ c) :: Γ ⊢[PRAAx] neg (r ≐ selected E R H c c) :=
          .impI (.impE notTag.wk (selectedTag.wk.eqTrans (congrSucc Prf.hyp0).eqSymm))
        exact (recode_congr (next_pivot_zero E R N H c c r (matrix_shape _ _ _ _ hA.wk.wk)
          hc.wk.wk Prf.hyp0 hr.wk.wk different)).eqTrans
          (recode_eq _ GaussianRationalSyntheticDivision.qzero_canonical)
    exact ((pivot_congr_matrix same.wk r j).eqTrans (recode_congr
      (entry_congr (.eqRefl _) Prf.hyp0))).eqTrans column

private theorem advanced_row (A R N c r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] lt c N) (hr : Γ ⊢[PRAAx] lt r R)
    (hu : Γ ⊢[PRAAx] unmarked (history A R N (succ c)) (succ c) r)
    (h : Γ ⊢[PRAAx] zeroRows (matrix A R N c) (history A R N c) R c) : Γ ⊢[PRAAx] .all
    (lt (var 0) (succ (Syn.shift c)) ⟶
      pivot (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (succ (Syn.shift c))) (Syn.shift r) (var 0) ≐ qzero) := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hcs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift c) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hc.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift R) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  have hus : Γ.map Fm.shift ⊢[PRAAx] unmarked (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (succ (Syn.shift c)))
      (succ (Syn.shift c)) (Syn.shift r) := by simpa [Fm.shift,Syn.shift] using hu.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] zeroRows (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c))
      (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c)) (Syn.shift R) (Syn.shift c) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  exact advanced_zero_at (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c) (Syn.shift r) (var 0)
    hAs.wk hcs.wk hrs.wk hus.wk Prf.hyp0 hs.wk

theorem advanced_rows (A R N c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hc : Γ ⊢[PRAAx] lt c N)
    (h : Γ ⊢[PRAAx] zeroRows (matrix A R N c) (history A R N c) R c) :
    Γ ⊢[PRAAx] zeroRows (matrix A R N (succ c)) (history A R N (succ c)) R (succ c) := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hcs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift c) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hc.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] zeroRows (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c))
      (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c)) (Syn.shift R) (Syn.shift c) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI (.impI ?_))
  simpa [Syn.shift] using
    advanced_row (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c) (var 0)
      hAs.wk.wk hcs.wk.wk Prf.hyp1 Prf.hyp0 hs.wk.wk

def prefixLaw (A R N c : PTm n) : Fm PTm n := le c N ⟶ zeroRows (matrix A R N c) (history A R N c) R c
def prefixSyntax (A R N c : PTm n) : BFm n := .imp (.le c N) (zeroRowsSyntax (matrix A R N c) (history A R N c) R c)
theorem prefix_formula (A R N c : PTm n) : formula (prefixSyntax A R N c) = prefixLaw A R N c := rfl
@[simp] theorem subst_prefixLaw {k : ℕ} (σ : Fin n → PTm k) (A R N c : PTm n) :
    (prefixLaw A R N c).subst σ = prefixLaw (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ c) := by
  simp [prefixLaw]

theorem prefix_zero_rows (A R N c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hc : Γ ⊢[PRAAx] le c N) :
    Γ ⊢[PRAAx] zeroRows (matrix A R N c) (history A R N c) R c := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  let S := prefixSyntax (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,prefix_formula,subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI (.allI (.impI (.impI (.allI (.impI ?_)))))
      have e : Syn.shift (Syn.shift (zero : PTm n)) = (zero : PTm (n + 2)) := by simp [Syn.shift]
      rw [e]
      exact .botE _ (lt_zero_absurd _ Prf.hyp0)
    · simp only [S,prefix_formula,subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact advanced_rows (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) hAs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have atC : Γ ⊢[PRAAx] prefixLaw A R N c := by simpa using all.allE c
  exact .impE atC hc

theorem actual_unmarked_row_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶ zeroRows (matrix (var 0) (var 1) (var 2) (var 3))
      (history (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (prefix_zero_rows _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalEliminationUnmarkedRows
