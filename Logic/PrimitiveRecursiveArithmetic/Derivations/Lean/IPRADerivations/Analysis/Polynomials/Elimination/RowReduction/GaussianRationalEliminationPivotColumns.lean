import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationUnmarkedRows

/-!
# Tagged pivot columns of the computed elimination

Each marked column has a unit at its tagged row and zero at every other
row. The actual pivot scan gives these entries when the column is first
processed. The unmarked-row invariant preserves them at every later step.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalEliminationPivotColumns

open_ipra
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical)
open GaussianRationalRowElimination (pivot shape)
open GaussianRationalEliminationLoop (matrix history matrix_succ history_pivot history_skip history_previous matrix_shape)
open GaussianRationalEliminationUnmarkedRows (prefix_zero_rows row_zero_at pivot_congr_matrix)
open GaussianRationalPivotSearch (flag flag_cases selected selected_correct next)
open GaussianTranslatedNonconstant (recode_congr recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem previous_column_value (A R N c j r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] lt c N) (hj : Γ ⊢[PRAAx] lt j c) (hr : Γ ⊢[PRAAx] lt r R) :
    Γ ⊢[PRAAx] pivot (matrix A R N (succ c)) r j ≐ pivot (matrix A R N c) r j := by
  let E := matrix A R N c
  let H := history A R N c
  have hPrefix := prefix_zero_rows A R N c hA (le_trans (le_succ_self c) hc)
  have zeroAtPivot : Γ ⊢[PRAAx] flag E R H c c ≐ one ⟶ pivot E (selected E R H c c) j ≐ qzero := by
    refine .impI ?_
    have sel := selected_correct (Γ := (flag E R H c c ≐ one) :: Γ) E R H c c Prf.hyp0
    exact row_zero_at E H R c (selected E R H c c) j hPrefix.wk (.andE₁ sel) (.andE₁ (.andE₂ sel)) hj.wk
  exact (pivot_congr_matrix (matrix_succ A R N c) r j).eqTrans
    (GaussianRationalEliminationZeroColumn.next_preserves_column E R N H c c r j hr
      (le_trans hj (le_trans (le_succ_self c) hc)) zeroAtPivot)

def delta (t v r : PTm n) : Fm PTm n :=
  (t ≐ succ r ⟶ v ≐ qone) ⋏ (neg (t ≐ zero) ⟶ neg (t ≐ succ r) ⟶ v ≐ qzero)

ipra_subst delta

theorem delta_transport {t t' v v' r : PTm n} (ht : Γ ⊢[PRAAx] t' ≐ t) (hv : Γ ⊢[PRAAx] v' ≐ v)
    (h : Γ ⊢[PRAAx] delta t v r) : Γ ⊢[PRAAx] delta t' v' r := by
  refine .andI (.impI ?_) (.impI (.impI ?_))
  · exact hv.wk.eqTrans (.impE (.andE₁ h.wk) (ht.wk.eqSymm.eqTrans Prf.hyp0))
  · have nonzero : neg (t' ≐ succ r) :: neg (t' ≐ zero) :: Γ ⊢[PRAAx] neg (t ≐ zero) :=
      .impI (.impE Prf.hyp1.wk (ht.wk.wk.wk.eqTrans Prf.hyp0))
    have other : neg (t' ≐ succ r) :: neg (t' ≐ zero) :: Γ ⊢[PRAAx] neg (t ≐ succ r) :=
      .impI (.impE Prf.hyp1 (ht.wk.wk.wk.eqTrans Prf.hyp0))
    exact hv.wk.wk.eqTrans (.impE (.impE (.andE₂ h.wk.wk) nonzero) other)

theorem new_column_delta (A R N c r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] lt c N) (hr : Γ ⊢[PRAAx] lt r R) :
    Γ ⊢[PRAAx] delta (entry (history A R N (succ c)) c) (pivot (matrix A R N (succ c)) r c) r := by
  let E := matrix A R N c
  let H := history A R N c
  let t := entry (history A R N (succ c)) c
  let s := selected E R H c c
  let f := flag E R H c c
  have cellEq := matrix_succ (Γ := Γ) A R N c
  have shaped := matrix_shape A R N c hA
  refine .orE (flag_cases E R H c c) ?_ ?_
  · have skipped := history_skip (Γ := (f ≐ zero) :: Γ) A R N c Prf.hyp0
    exact .andI (.impI (.botE _ (succ_ne_zero (Prf.hyp0.eqSymm.eqTrans skipped.wk))))
      (.impI (.botE _ (.impE Prf.hyp0 skipped.wk)))
  · have tagged := history_pivot (Γ := (f ≐ one) :: Γ) A R N c Prf.hyp0
    have unitCell := GaussianRationalPivotSearch.next_pivot_one (Γ := (f ≐ one) :: Γ) E R N H c c shaped.wk hc.wk Prf.hyp0
    refine .andI (.impI ?_) (.impI (.impI ?_))
    · have sameRow : (t ≐ succ r) :: (f ≐ one) :: Γ ⊢[PRAAx] r ≐ s :=
        succ_inj (Prf.hyp0.eqSymm.eqTrans tagged.wk)
      have rowEq := entry_congr (entry_congr cellEq.wk.wk sameRow) (.eqRefl c)
      exact (recode_congr (rowEq.eqTrans unitCell.wk)).eqTrans (recode_eq _ qone_canonical)
    · have offRow : neg (t ≐ succ r) :: neg (t ≐ zero) :: (f ≐ one) :: Γ ⊢[PRAAx] neg (r ≐ s) :=
        .impI (.impE Prf.hyp1 (tagged.wk.wk.wk.eqTrans (congrSucc Prf.hyp0).eqSymm))
      have atZero := GaussianRationalPivotSearch.next_pivot_zero E R N H c c r shaped.wk.wk.wk hc.wk.wk.wk
        (Prf.hyp1.wk (ψ := neg (t ≐ succ r))) hr.wk.wk.wk offRow
      exact (pivot_congr_matrix cellEq.wk.wk.wk r c).eqTrans
        ((recode_congr atZero).eqTrans (recode_eq _ qzero_canonical))

def columnLaw (A R N c j r : PTm n) : Fm PTm n := le c N ⟶ lt j c ⟶
  delta (entry (history A R N c) j) (pivot (matrix A R N c) r j) r

ipra_subst columnLaw

theorem next_column_delta (A R N c j r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] lt c N) (hj : Γ ⊢[PRAAx] lt j (succ c)) (hr : Γ ⊢[PRAAx] lt r R)
    (h : Γ ⊢[PRAAx] columnLaw A R N c j r) :
    Γ ⊢[PRAAx] delta (entry (history A R N (succ c)) j) (pivot (matrix A R N (succ c)) r j) r := by
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hj)) ?_ ?_
  · exact delta_transport (history_previous A R N c j Prf.hyp0)
      (previous_column_value A R N c j r hA.wk hc.wk Prf.hyp0 hr.wk)
      (.impE (.impE h.wk (le_trans (le_succ_self c) hc.wk)) Prf.hyp0)
  · exact delta_transport (entry_congr (.eqRefl _) Prf.hyp0)
      (recode_congr (entry_congr (.eqRefl _) Prf.hyp0)) (new_column_delta A R N c r hA.wk hc.wk hr.wk)

theorem prefix_column_delta (A R N c j r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] le c N) (hj : Γ ⊢[PRAAx] lt j c) (hr : Γ ⊢[PRAAx] lt r R) :
    Γ ⊢[PRAAx] delta (entry (history A R N c) j) (pivot (matrix A R N c) r j) r := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift R) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  have all : Γ ⊢[PRAAx] .all (columnLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift j) (Syn.shift r)) := by
    ipra_qfind (by simp [columnLaw,delta,Fm.QF,neg,le,lt]) [subst_columnLaw]
    · exact .impI (.impI (.botE _ (lt_zero_absurd _ Prf.hyp0)))
    · exact .impI (.impI (next_column_delta (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift j)
        (Syn.shift r) hAs.wk.wk.wk Prf.hyp1 Prf.hyp0 hrs.wk.wk.wk Prf.hyp1.wk))
  have atC : Γ ⊢[PRAAx] columnLaw A R N c j r := by simpa using all.allE c
  exact .impE (.impE atC hc) hj

theorem pivot_one_at (A R N c j r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hc : Γ ⊢[PRAAx] le c N)
    (hj : Γ ⊢[PRAAx] lt j c) (hr : Γ ⊢[PRAAx] lt r R) (ht : Γ ⊢[PRAAx] entry (history A R N c) j ≐ succ r) :
    Γ ⊢[PRAAx] pivot (matrix A R N c) r j ≐ qone :=
  .impE (.andE₁ (prefix_column_delta A R N c j r hA hc hj hr)) ht

theorem pivot_zero_at (A R N c j r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hc : Γ ⊢[PRAAx] le c N)
    (hj : Γ ⊢[PRAAx] lt j c) (hr : Γ ⊢[PRAAx] lt r R) (hn : Γ ⊢[PRAAx] neg (entry (history A R N c) j ≐ zero))
    (hd : Γ ⊢[PRAAx] neg (entry (history A R N c) j ≐ succ r)) :
    Γ ⊢[PRAAx] pivot (matrix A R N c) r j ≐ qzero :=
  .impE (.impE (.andE₂ (prefix_column_delta A R N c j r hA hc hj hr)) hn) hd

theorem actual_previous_column_preserved_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ lt (var 3) (var 2) ⟶ lt (var 4) (var 3) ⟶ lt (var 5) (var 1) ⟶
      pivot (matrix (var 0) (var 1) (var 2) (succ (var 3))) (var 5) (var 4) ≐
      pivot (matrix (var 0) (var 1) (var 2) (var 3)) (var 5) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (previous_column_value _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_pivot_column_delta_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶ lt (var 4) (var 3) ⟶ lt (var 5) (var 1) ⟶
      delta (entry (history (var 0) (var 1) (var 2) (var 3)) (var 4))
        (pivot (matrix (var 0) (var 1) (var 2) (var 3)) (var 5) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (prefix_column_delta _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalEliminationPivotColumns
