import IPRADerivations.Analysis.LinearAlgebra.Cofactors.GaussianRationalFreeColumnVector
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalPivotHistoryCount
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationTagProfile
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationUnmarkedRows
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationPivotColumns

/-!
# An actual nonzero annihilator from a deficient computed pivot count

The original numerical matrix is eliminated by the actual column loop.
Its own history supplies the least free column and the actual vector.
The proved tag/cell profiles derive that every reduced row has zero dot
product; actual backward null transport gives the original equations.

Only original rectangular shape and a deficit in the actual computed
marked-column count are inputs. No final profile, free-search success,
null-vector or nonzero-vector conclusion is a producer premise. This
does not identify that numerical count with an external rank interface.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalAnnihilatorVector

open_ipra
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalRowElimination (shape pivot rowDot nullRows)
open GaussianRationalEliminationLoop (matrix history)
open GaussianRationalFreeColumnVector (freeInput nonzeroVector pivotProfile fieldZeroRow)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finalMatrix (A R N : PTm n) : PTm n := matrix A R N N
def finalHistory (A R N : PTm n) : PTm n := history A R N N
def markedCount (A R N : PTm n) : PTm n := GaussianRationalPivotHistoryCount.count (finalHistory A R N) N
def freeColumn (A R N : PTm n) : PTm n := GaussianRationalPivotHistoryCount.free (finalHistory A R N) N
def vector (A R N : PTm n) : PTm n :=
  GaussianRationalFreeColumnVector.run (finalMatrix A R N) (finalHistory A R N) N (freeColumn A R N)
def input (A R N : PTm n) : Fm PTm n := shape A R N ⋏ lt (markedCount A R N) N
def certificate (A R N v : PTm n) : Fm PTm n := length v ≐ N ⋏ (nonzeroVector v N ⋏ nullRows A R N v)

ipra_subst finalMatrix
ipra_subst finalHistory
ipra_subst markedCount
ipra_subst freeColumn
ipra_subst vector
ipra_subst input
ipra_subst certificate

theorem free_correct (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] freeInput (finalHistory A R N) N (freeColumn A R N) :=
  GaussianRationalPivotHistoryCount.free_correct (finalHistory A R N) N (.andE₂ h)
theorem vector_length (A R N : PTm n) : Γ ⊢[PRAAx] length (vector A R N) ≐ N :=
  GaussianRationalFreeColumnVector.returned_length _ _ _ _
theorem selected_one (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] entry (vector A R N) (freeColumn A R N) ≐ qone :=
  GaussianRationalFreeColumnVector.returned_selected _ _ _ _ (.andE₁ (free_correct A R N h))
theorem vector_nonzero (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] nonzeroVector (vector A R N) N :=
  GaussianRationalFreeColumnVector.returned_nonzero _ _ _ _ (.andE₁ (free_correct A R N h))

theorem other_marked_zero (A R N r p j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hr : Γ ⊢[PRAAx] lt r R) (hp : Γ ⊢[PRAAx] lt p N)
    (hTag : Γ ⊢[PRAAx] entry (finalHistory A R N) p ≐ succ r)
    (hj : Γ ⊢[PRAAx] lt j N) (hne : Γ ⊢[PRAAx] neg (j ≐ p))
    (hNZ : Γ ⊢[PRAAx] neg (entry (finalHistory A R N) j ≐ zero)) :
    Γ ⊢[PRAAx] pivot (finalMatrix A R N) r j ≐ qzero := by
  have different : Γ ⊢[PRAAx] neg (entry (finalHistory A R N) j ≐ succ r) := by
    refine .impI (.impE hne.wk ?_)
    exact GaussianRationalEliminationTagProfile.equal_tags_unique A R N N j p hj.wk hp.wk hNZ.wk
      (Prf.hyp0.eqTrans hTag.wk.eqSymm)
  exact GaussianRationalEliminationPivotColumns.pivot_zero_at A R N N j r hA (le_refl N) hj hr hNZ different

theorem reduced_pivot_profile (A R N r p : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hr : Γ ⊢[PRAAx] lt r R) (hp : Γ ⊢[PRAAx] lt p N)
    (hTag : Γ ⊢[PRAAx] entry (finalHistory A R N) p ≐ succ r) : Γ ⊢[PRAAx]
    pivotProfile (finalMatrix A R N) (finalHistory A R N) N r p := by
  refine .andI (.andI hp hTag) (.andI
    (GaussianRationalEliminationPivotColumns.pivot_one_at A R N N p r hA (le_refl N) hp hr hTag) ?_)
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have hps : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift p) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hp.shift
  have tags : Γ.map Fm.shift ⊢[PRAAx] entry (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift p) ≐ succ (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using hTag.shift
  refine .allI (.impI (.impI (.impI ?_)))
  simpa only [Syn.shift,subst_finalMatrix,subst_finalHistory,pivot] using
    other_marked_zero (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift r) (Syn.shift p) (var 0)
      hAs.wk.wk.wk hrs.wk.wk.wk hps.wk.wk.wk tags.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

theorem reduced_unmarked_row (A R N r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hr : Γ ⊢[PRAAx] lt r R)
    (hu : Γ ⊢[PRAAx] GaussianRationalPivotSearch.unmarked (finalHistory A R N) N r) :
    Γ ⊢[PRAAx] fieldZeroRow (finalMatrix A R N) N r := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have hus : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalPivotSearch.unmarked
      (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift N) (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using hu.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_finalMatrix,finalMatrix,GaussianRationalEliminationLoop.subst_matrix,pivot] using
    GaussianRationalEliminationUnmarkedRows.row_zero_at
      (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift N))
      (history (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift N)) (Syn.shift R) (Syn.shift N) (Syn.shift r) (var 0)
      (GaussianRationalEliminationUnmarkedRows.prefix_zero_rows _ _ _ _ hAs.wk (le_refl _)) hrs.wk hus.wk Prf.hyp0

theorem reduced_row_null (A R N r : PTm n) (h : Γ ⊢[PRAAx] input A R N) (hr : Γ ⊢[PRAAx] lt r R) :
    Γ ⊢[PRAAx] rowDot (finalMatrix A R N) N (vector A R N) r ≐ qzero := by
  refine .orE (GaussianRationalPivotSearch.available_cases (finalHistory A R N) N r) ?_ ?_
  · have hit := GaussianRationalEliminationTagProfile.row_column_found (Γ :=
      (GaussianRationalPivotSearch.available (finalHistory A R N) N r ≐ zero) :: Γ) A R N N r Prf.hyp0
    exact GaussianRationalFreeColumnVector.returned_pivot_null _ _ _ _ _ _ (free_correct A R N h.wk)
      (reduced_pivot_profile A R N r (GaussianRationalEliminationTagProfile.rowColumn A R N N r)
        (.andE₁ h.wk) hr.wk (.andE₁ hit) (.andE₁ (.andE₂ hit)))
  · exact GaussianRationalFreeColumnVector.field_zero_row_dot _ _ _ _
      (reduced_unmarked_row A R N r (.andE₁ h.wk) hr.wk
        (GaussianRationalPivotSearch.available_unmarked _ _ _ Prf.hyp0))

theorem reduced_null_rows (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] nullRows (finalMatrix A R N) R N (vector A R N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_finalMatrix,subst_vector] using
    reduced_row_null (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) hs.wk Prf.hyp0
theorem original_null_rows (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] nullRows A R N (vector A R N) :=
  (GaussianRationalEliminationLoop.final_null_equivalence A R N (vector A R N) (.andE₁ h)).iffMpr
    (reduced_null_rows A R N h)
theorem vector_correct (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] certificate A R N (vector A R N) :=
  .andI (vector_length A R N) (.andI (vector_nonzero A R N h) (original_null_rows A R N h))

def vectorF : PR 3 := PTm.toPR (vector (var 0) (var 1) (var 2))
def run (A R N : PTm n) : PTm n := app vectorF ![A,R,N]
ipra_subst run
theorem program_at (A R N : PTm n) : Γ ⊢[PRAAx] run A R N ≐ vector A R N := by
  simpa [run,vectorF] using toPR_eq (Γ := Γ) (vector (var 0) (var 1) (var 2) : PTm 3) ![A,R,N]
theorem certificate_congr {A R N v w : PTm n} (e : Γ ⊢[PRAAx] v ≐ w) (h : Γ ⊢[PRAAx] certificate A R N v) :
    Γ ⊢[PRAAx] certificate A R N w := by
  simpa only [subst_certificate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (certificate (var 0) (var 1) (var 2) (var 3) : Fm PTm 4) ![A,R,N,v] ![A,R,N,w]
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact e)
      (by simpa only [subst_certificate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using h)
theorem returned_certificate (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) :
    Γ ⊢[PRAAx] certificate A R N (run A R N) := certificate_congr (program_at A R N).eqSymm (vector_correct A R N h)

theorem actual_vector_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (vector (var 0) (var 1) (var 2)) ≐ var 2) := closeUniv 3 (vector_length _ _ _)
theorem actual_computed_free_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ freeInput (finalHistory (var 0) (var 1) (var 2)) (var 2)
      (freeColumn (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (free_correct _ _ _ Prf.hyp0))
theorem actual_nonzero_vector_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ nonzeroVector (vector (var 0) (var 1) (var 2)) (var 2)) :=
  closeUniv 3 (.impI (vector_nonzero _ _ _ Prf.hyp0))
theorem actual_reduced_null_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ nullRows (finalMatrix (var 0) (var 1) (var 2)) (var 1) (var 2)
      (vector (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (reduced_null_rows _ _ _ Prf.hyp0))
theorem actual_original_null_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ nullRows (var 0) (var 1) (var 2) (vector (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_null_rows _ _ _ Prf.hyp0))
theorem actual_annihilator_vector_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (vector (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (vector_correct _ _ _ Prf.hyp0))
theorem actual_vector_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ vector (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_annihilator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (run (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (returned_certificate _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalAnnihilatorVector
