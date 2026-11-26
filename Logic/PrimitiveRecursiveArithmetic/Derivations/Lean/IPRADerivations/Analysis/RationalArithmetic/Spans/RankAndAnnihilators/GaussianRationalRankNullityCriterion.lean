import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationPivotColumns
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalEliminationTagProfile
import IPRADerivations.Analysis.RationalArithmetic.Spans.Pivoting.GaussianRationalPivotHistoryCount
import IPRADerivations.Analysis.LinearAlgebra.Cofactors.GaussianRationalFreeColumnVector
import IPRADerivations.Analysis.LinearAlgebra.Cofactors.GaussianRationalAnnihilatorVector

/-!
# Full computed pivot count and the actual right kernel

The actual reduced pivot-column delta extracts each original numerical
vector coordinate from one real row dot. Full marked count therefore
forces every original homogeneous null vector to vanish as FIELD values.
The converse obstruction derives a deficit from any real nonzero null
vector. The exact numerical deficit is equivalent to an actual nonzero
length-N null vector, using the proved producer in the forward direction.
No abstract rank interface or final profile is an input. No general
row-space dimension formula is asserted.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRankNullityCriterion

open_ipra
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalRowElimination (shape pivot rowDot nullRows)
open GaussianRationalEliminationLoop (matrix history)
open GaussianRationalPivotHistoryCount (count allMarked allMarked_at count_lt_of_zero count_bound)
open GaussianRationalFreeColumnVector (pivotRow nonzeroVector)
open GaussianTranslatedNonconstant (recode recode_congr)
open GaussianRationalFiberVandermonde (delta)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finalMatrix (A R N : PTm n) : PTm n := matrix A R N N
def finalHistory (A R N : PTm n) : PTm n := history A R N N
def rank (A R N : PTm n) : PTm n := count (finalHistory A R N) N
def zeroVector (v N : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ recode (entry (Syn.shift v) (var 0)) ≐ qzero)
def reader : PTm 2 := entry (var 1) (var 0)
ipra_subst finalMatrix
ipra_subst finalHistory
ipra_subst rank
ipra_subst zeroVector [Syn.subst_shift, Syn.shift_subst]

theorem count_full_marked (H N : PTm n) (hFull : Γ ⊢[PRAAx] count H N ≐ N) : Γ ⊢[PRAAx] allMarked H N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] count (Syn.shift H) (Syn.shift N) ≐ Syn.shift N := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalPivotHistoryCount.subst_count,Syn.shift] using hFull.shift
  refine .allI (.impI (.impI ?_))
  have bad : (entry (Syn.shift H) (var 0) ≐ zero) :: lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (count (Syn.shift H) (Syn.shift N)) (Syn.shift N) := count_lt_of_zero _ _ _ Prf.hyp1 Prf.hyp0
  exact lt_irrefl _ _ (lt_congr hs.wk.wk (.eqRefl _) bad)

theorem positive_tag_row (H j : PTm n) (hNZ : Γ ⊢[PRAAx] neg (entry H j ≐ zero)) : Γ ⊢[PRAAx]
    entry H j ≐ succ (pivotRow H j) := by
  refine .orE (zero_or_succ (entry H j)) ?_ ?_
  · exact .botE _ (.impE hNZ.wk Prf.hyp0)
  · exact Prf.hyp0.eqTrans (congrSucc (GaussianRationalFreeColumnVector.pivot_row_at H j (pred (entry H j)) Prf.hyp0)).eqSymm

theorem tag_row_bound (A R N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hNZ : Γ ⊢[PRAAx] neg (entry (finalHistory A R N) j ≐ zero)) : Γ ⊢[PRAAx]
    lt (pivotRow (finalHistory A R N) j) R :=
  le_congr (positive_tag_row _ _ hNZ) (.eqRefl _) (GaussianRationalEliminationTagProfile.tag_bound A R N N j hj)

theorem full_marked_cell (A R N j k : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hMarked : Γ ⊢[PRAAx] allMarked (finalHistory A R N) N)
    (hj : Γ ⊢[PRAAx] lt j N) (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx]
    pivot (finalMatrix A R N) (pivotRow (finalHistory A R N) j) k ≐ delta j k := by
  let H := finalHistory A R N
  let r := pivotRow H j
  have jNZ := allMarked_at H N j hMarked hj
  have tagJ := positive_tag_row H j jNZ
  have hr := tag_row_bound A R N j hj jNZ
  refine .orE (eq_or_ne k j) ?_ ?_
  · exact (recode_congr (entry_congr (.eqRefl _) Prf.hyp0)).eqTrans
      ((GaussianRationalEliminationPivotColumns.pivot_one_at A R N N j r hA.wk (le_refl N) hj.wk hr.wk tagJ.wk).eqTrans
        (GaussianRationalLagrangeCardinals.delta_equal j k Prf.hyp0.eqSymm).eqSymm)
  · have kNZ := allMarked_at (Γ := neg (k ≐ j) :: Γ) H N k hMarked.wk hk.wk
    have other : neg (k ≐ j) :: Γ ⊢[PRAAx] neg (entry H k ≐ succ r) := by
      refine .impI (.impE Prf.hyp1 ?_)
      exact GaussianRationalEliminationTagProfile.equal_tags_unique A R N N k j hk.wk.wk hj.wk.wk kNZ.wk
        (Prf.hyp0.eqTrans tagJ.wk.wk.eqSymm)
    have different : neg (k ≐ j) :: Γ ⊢[PRAAx] neg (j ≐ k) := .impI (.impE Prf.hyp1 Prf.hyp0.eqSymm)
    exact (GaussianRationalEliminationPivotColumns.pivot_zero_at A R N N k r hA.wk (le_refl N) hk.wk hr.wk kNZ other).eqTrans
      (GaussianRationalLagrangeCardinals.delta_unequal j k different).eqSymm

theorem reader_at (v j : PTm n) : inst2 reader j v = entry v j := by simp [reader,inst2]

theorem full_marked_dot_coordinate (A R N v j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hMarked : Γ ⊢[PRAAx] allMarked (finalHistory A R N) N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    rowDot (finalMatrix A R N) N v (pivotRow (finalHistory A R N) j) ≐ recode (entry v j) := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have hMs : Γ.map Fm.shift ⊢[PRAAx] allMarked (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hMarked.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hj.shift
  have same : Γ ⊢[PRAAx] rowDot (finalMatrix A R N) N v (pivotRow (finalHistory A R N) j) ≐
      GaussianRationalMatrixFiniteSums.deltaSum reader N j v := by
    refine GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalRowElimination.dotBody
      (GaussianRationalMatrixFiniteSums.deltaBody reader) N
      (GaussianRationalRowElimination.dotData (finalMatrix A R N) v (pivotRow (finalHistory A R N) j)) (pairT j v) ?_
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have low := (GaussianRationalRowElimination.dot_body_at (Γ := Δ) (finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (Syn.shift v) (pivotRow (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift j)) (var 0)).eqTrans
      ((GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _).eqSymm.eqTrans
        (qmul_congr (full_marked_cell _ _ _ _ _ hAs.wk hMs.wk hjs.wk Prf.hyp0) (.eqRefl _)))
    have high := GaussianRationalMatrixFiniteSums.delta_body_at (Γ := Δ) reader (Syn.shift j) (var 0) (Syn.shift v)
    simp only [reader_at] at high
    simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_dotData,subst_finalMatrix,subst_finalHistory,
      GaussianRationalFreeColumnVector.subst_pivotRow,subst_pairT,reader_at] using low.eqTrans high.eqSymm
  exact same.eqTrans (by simpa only [reader_at] using GaussianRationalMatrixFiniteSums.sum_delta (Γ := Γ) reader N j v hj)

theorem full_count_null_zero_at (A R N v j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hFull : Γ ⊢[PRAAx] rank A R N ≐ N) (hNull : Γ ⊢[PRAAx] nullRows A R N v) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    recode (entry v j) ≐ qzero := by
  have marked := count_full_marked (finalHistory A R N) N hFull
  have jNZ := allMarked_at (finalHistory A R N) N j marked hj
  have reduced := (GaussianRationalEliminationLoop.final_null_equivalence A R N v hA).iffMp hNull
  exact (full_marked_dot_coordinate A R N v j hA marked hj).eqSymm.eqTrans
    (GaussianRationalRowElimination.null_at (finalMatrix A R N) R N v (pivotRow (finalHistory A R N) j) reduced
      (tag_row_bound _ _ _ _ hj jNZ))

theorem full_count_null_zero (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hFull : Γ ⊢[PRAAx] rank A R N ≐ N) (hNull : Γ ⊢[PRAAx] nullRows A R N v) : Γ ⊢[PRAAx] zeroVector v N := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have hFs : Γ.map Fm.shift ⊢[PRAAx] rank (Syn.shift A) (Syn.shift R) (Syn.shift N) ≐ Syn.shift N := by
    simpa [Fm.shift,Syn.shift] using hFull.shift
  have hNs : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v) := by
    simpa [Fm.shift,Syn.shift] using hNull.shift
  refine .allI (.impI ?_)
  exact full_count_null_zero_at (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v) (var 0) hAs.wk hFs.wk hNs.wk Prf.hyp0

theorem zero_vector_at (v N j : PTm n) (h : Γ ⊢[PRAAx] zeroVector v N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    recode (entry v j) ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ recode (entry v j) ≐ qzero := by simpa [zeroVector] using h.allE j
  exact .impE rule hj

theorem zero_nonzero_absurd (v N : PTm n) (hZ : Γ ⊢[PRAAx] zeroVector v N) (hNZ : Γ ⊢[PRAAx] nonzeroVector v N) : Γ ⊢[PRAAx] .bot := by
  have hZs : Γ.map Fm.shift ⊢[PRAAx] zeroVector (Syn.shift v) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hZ.shift
  refine .exE hNZ ?_
  let Δ := (lt (var 0) (Syn.shift N) ⋏ neg (recode (entry (Syn.shift v) (var 0)) ≐ qzero)) :: Γ.map Fm.shift
  exact .impE (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _)) (zero_vector_at _ _ _ hZs.wk (.andE₁ Prf.hyp0))

theorem nonzero_null_implies_deficit (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hNull : Γ ⊢[PRAAx] nullRows A R N v) (hNZ : Γ ⊢[PRAAx] nonzeroVector v N) : Γ ⊢[PRAAx] lt (rank A R N) N := by
  refine .orE (lt_or_eq_of_le (count_bound (finalHistory A R N) N)) Prf.hyp0 ?_
  exact .botE _ (zero_nonzero_absurd v N (full_count_null_zero A R N v hA.wk Prf.hyp0 hNull.wk) hNZ.wk)

/-! The numerical vector existential is an ordinary source-language
formula. It is never used as an induction formula. -/
def hasNonzeroNull (A R N : PTm n) : Fm PTm n := .ex
  ((length (var 0) ≐ Syn.shift N) ⋏ (nonzeroVector (var 0) (Syn.shift N) ⋏
    nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)))
ipra_subst hasNonzeroNull [Syn.subst_shift, Syn.shift_subst]

theorem deficit_has_nonzero_null (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hDef : Γ ⊢[PRAAx] lt (rank A R N) N) : Γ ⊢[PRAAx] hasNonzeroNull A R N := by
  refine .exI (GaussianRationalAnnihilatorVector.run A R N) ?_
  simpa only [hasNonzeroNull,Fm.subst_and,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
    GaussianRationalFreeColumnVector.subst_nonzeroVector,GaussianRationalRowElimination.subst_nullRows,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,GaussianRationalAnnihilatorVector.certificate] using
      GaussianRationalAnnihilatorVector.returned_certificate A R N (.andI hA hDef)

theorem has_nonzero_null_implies_deficit (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (h : Γ ⊢[PRAAx] hasNonzeroNull A R N) : Γ ⊢[PRAAx] lt (rank A R N) N := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hA.shift
  refine .exE h ?_
  let Δ := ((length (var 0) ≐ Syn.shift N) ⋏ (nonzeroVector (var 0) (Syn.shift N) ⋏
    nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0))) :: Γ.map Fm.shift
  simpa only [Δ,Fm.shift,subst_lt,subst_rank,Syn.shift] using
    nonzero_null_implies_deficit (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) hAs.wk
      (Prf.andE₂ (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _))) (.andE₁ (.andE₂ Prf.hyp0))

theorem rank_deficiency_iff_nonzero_null (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    Fm.iff (lt (rank A R N) N) (hasNonzeroNull A R N) :=
  .andI (.impI (deficit_has_nonzero_null A R N hA.wk Prf.hyp0))
    (.impI (has_nonzero_null_implies_deficit A R N hA.wk Prf.hyp0))

theorem rank_bound (A R N : PTm n) : Γ ⊢[PRAAx] le (rank A R N) N := count_bound _ _
theorem rank_zero (A R : PTm n) : Γ ⊢[PRAAx] rank A R zero ≐ zero := GaussianRationalPivotHistoryCount.count_zero _

def rankF : PR 3 := PTm.toPR (rank (var 0) (var 1) (var 2))
def run (A R N : PTm n) : PTm n := app rankF ![A,R,N]
ipra_subst run
theorem program_at (A R N : PTm n) : Γ ⊢[PRAAx] run A R N ≐ rank A R N := by
  simpa [run,rankF] using toPR_eq (Γ := Γ) (rank (var 0) (var 1) (var 2) : PTm 3) ![A,R,N]
theorem returned_criterion (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    Fm.iff (lt (run A R N) N) (hasNonzeroNull A R N) := by
  have criterion := rank_deficiency_iff_nonzero_null A R N hA
  exact .andI (.impI (criterion.wk.iffMp (lt_congr (program_at _ _ _).wk (.eqRefl _) Prf.hyp0)))
    (.impI (lt_congr (program_at _ _ _).wk.eqSymm (.eqRefl _) (criterion.wk.iffMpr Prf.hyp0)))

theorem actual_full_count_marked_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (count (var 0) (var 1) ≐ var 1 ⟶ allMarked (var 0) (var 1)) := closeUniv 2 (.impI (count_full_marked _ _ Prf.hyp0))
theorem actual_full_marked_dot_coordinate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (var 0) (var 1) (var 2) ⟶ allMarked (finalHistory (var 0) (var 1) (var 2)) (var 2) ⟶ lt (var 4) (var 2) ⟶
      rowDot (finalMatrix (var 0) (var 1) (var 2)) (var 2) (var 3) (pivotRow (finalHistory (var 0) (var 1) (var 2)) (var 4)) ≐
        recode (entry (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (full_marked_dot_coordinate _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_full_count_null_zero_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (var 0) (var 1) (var 2) ⟶ rank (var 0) (var 1) (var 2) ≐ var 2 ⟶ nullRows (var 0) (var 1) (var 2) (var 3) ⟶
      lt (var 4) (var 2) ⟶ recode (entry (var 3) (var 4)) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (full_count_null_zero_at _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_full_count_null_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ rank (var 0) (var 1) (var 2) ≐ var 2 ⟶ nullRows (var 0) (var 1) (var 2) (var 3) ⟶
      zeroVector (var 3) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (full_count_null_zero _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_nonzero_null_deficit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ nullRows (var 0) (var 1) (var 2) (var 3) ⟶ nonzeroVector (var 3) (var 2) ⟶
      lt (rank (var 0) (var 1) (var 2)) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (nonzero_null_implies_deficit _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rank_deficiency_criterion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (shape (var 0) (var 1) (var 2) ⟶ Fm.iff (lt (rank (var 0) (var 1) (var 2)) (var 2))
      (hasNonzeroNull (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (rank_deficiency_iff_nonzero_null _ _ _ Prf.hyp0))
theorem actual_rank_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (rank (var 0) (var 1) (var 2)) (var 2)) := closeUniv 3 (rank_bound _ _ _)
theorem actual_zero_columns_rank_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rank (var 0) (var 1) zero ≐ zero) := closeUniv 2 (rank_zero _ _)
theorem actual_rank_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ rank (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_criterion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (shape (var 0) (var 1) (var 2) ⟶ Fm.iff (lt (run (var 0) (var 1) (var 2)) (var 2))
      (hasNonzeroNull (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (returned_criterion _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalRankNullityCriterion
