import IPRADerivations.Analysis.GaussianRationalRankNullityCriterion
import IPRADerivations.Analysis.GaussianRationalRowSpan

/-!
# Spanning every vector when all columns have pivots

For each reduced row, read the target coordinate at the row's computed
pivot column. The tagged pivot columns make the resulting combination
equal to the target coordinate by coordinate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFullReducedSpan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalFiberVandermonde (delta)
open GaussianRationalLagrangeCardinals (delta_equal delta_unequal)
open GaussianRationalRowElimination (pivot shape)
open GaussianRationalRowSpan (columnBody columnData combinationAt witness)
open GaussianRationalEliminationTagProfile (rowColumn row_column_at)
open GaussianRationalFreeColumnVector (pivotRow)
open GaussianRationalRankNullityCriterion (rank finalMatrix finalHistory positive_tag_row tag_row_bound
  count_full_marked reader reader_at subst_finalMatrix subst_finalHistory)
open GaussianRationalPivotHistoryCount (allMarked allMarked_at)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianTranslatedNonconstant (recode recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (A R N v i : PTm n) : PTm n := entry v (rowColumn A R N N i)
def data (A R N v : PTm n) : PTm n := pairT A (pairT R (pairT N v))
def weightBody : PTm 2 := weight (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
  (sndT (sndT (sndT (var 1)))) (var 0)
def weights (A R N v : PTm n) : PTm n := sequence weightBody R (data A R N v)

@[simp] theorem subst_weight {k : ℕ} (σ : Fin n → PTm k) (A R N v i : PTm n) :
    Syn.subst σ (weight A R N v i) = weight (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ v) (Syn.subst σ i) := by simp [weight]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (data A R N v) = data (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by simp [data]
@[simp] theorem subst_weights {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (weights A R N v) = weights (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by simp [weights]

theorem weight_body_at (A R N v i : PTm n) : Γ ⊢[PRAAx] inst2 weightBody i (data A R N v) ≐ weight A R N v i := by
  have tail := snd_pair (Γ := Γ) A (pairT R (pairT N v))
  have endPair := (congrSnd tail).eqTrans (snd_pair R (pairT N v))
  simp only [weightBody,inst2,subst_weight,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa using Prf.eqCongr (Γ := Γ) (weight (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (data A R N v),fstT (sndT (data A R N v)),fstT (sndT (sndT (data A R N v))),
      sndT (sndT (sndT (data A R N v))),i])
    (σ' := ![A,R,N,v,i]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrFst endPair).eqTrans (fst_pair _ _)
      · exact (congrSnd endPair).eqTrans (snd_pair _ _)
      · exact .eqRefl _)

theorem weights_length (A R N v : PTm n) : Γ ⊢[PRAAx] length (weights A R N v) ≐ R := sequence_length _ _ _
theorem weights_lookup (A R N v i : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    entry (weights A R N v) i ≐ weight A R N v i :=
  (sequence_decode weightBody hi).eqTrans (weight_body_at _ _ _ _ _)

theorem tagged_column (A R N j i : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hj : Γ ⊢[PRAAx] lt j N)
    (hi : Γ ⊢[PRAAx] lt i R) (hn : Γ ⊢[PRAAx] neg (entry (finalHistory A R N) j ≐ ConciseIPRA.PTm.zero)) :
    Γ ⊢[PRAAx] pivot (finalMatrix A R N) i j ≐ delta (pivotRow (finalHistory A R N) j) i := by
  let h := finalHistory A R N
  let p := pivotRow h j
  have tag := positive_tag_row h j hn
  refine .orE (eq_or_ne p i) ?_ ?_
  · have matchTag : (p ≐ i) :: Γ ⊢[PRAAx] entry h j ≐ succ i := tag.wk.eqTrans (congrSucc Prf.hyp0)
    exact (GaussianRationalEliminationPivotColumns.pivot_one_at A R N N j i hA.wk (le_refl _) hj.wk hi.wk
      matchTag).eqTrans (delta_equal p i Prf.hyp0).eqSymm
  · have mismatch : neg (p ≐ i) :: Γ ⊢[PRAAx] neg (entry h j ≐ succ i) :=
      .impI (.impE Prf.hyp1 (succ_inj (tag.wk.wk.eqSymm.eqTrans Prf.hyp0)))
    exact (GaussianRationalEliminationPivotColumns.pivot_zero_at A R N N j i hA.wk (le_refl _) hj.wk hi.wk hn.wk
      mismatch).eqTrans (delta_unequal p i Prf.hyp0).eqSymm

theorem combination_coordinate (A R N v j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (h : Γ ⊢[PRAAx] allMarked (finalHistory A R N) N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (finalMatrix A R N) R (weights A R N v) j ≐ recode (entry v j) := by
  let H := finalHistory A R N
  let E := finalMatrix A R N
  let C := weights A R N v
  let p := pivotRow H j
  have hn := allMarked_at H N j h hj
  have tag := positive_tag_row H j hn
  have hp := tag_row_bound A R N j hj hn
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hj.shift
  have hns : Γ.map Fm.shift ⊢[PRAAx] neg (entry (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (Syn.shift j) ≐ ConciseIPRA.PTm.zero) := by simpa [Fm.shift,Syn.shift,H] using hn.shift
  have folded : Γ ⊢[PRAAx] combinationAt E R C j ≐ GaussianRationalMatrixFiniteSums.deltaSum reader R p C := by
    refine GaussianRationalFiniteSum.sum_congr_bounded columnBody (GaussianRationalMatrixFiniteSums.deltaBody reader) R (columnData E C j) (pairT p C)
      (.allI (.impI ?_))
    let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
    have col := tagged_column (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift j) (var 0)
      hAs.wk hjs.wk Prf.hyp0 hns.wk
    have low := GaussianRationalRowSpan.column_body_at (Γ := Δ)
      (finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v)) (Syn.shift j) (var 0)
    have high := GaussianRationalMatrixFiniteSums.delta_body_at (Γ := Δ) reader
      (pivotRow (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift j)) (var 0)
      (weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v))
    rw [reader_at] at high
    simpa only [Δ,Syn.shift,E,C,p,H,GaussianRationalRowSpan.subst_columnData,subst_finalMatrix,
      subst_finalHistory,subst_weights,GaussianRationalFreeColumnVector.subst_pivotRow,subst_pairT] using
      low.eqTrans ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqSymm.eqTrans
        ((qmul_congr (.eqRefl _) col).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans high.eqSymm)))
  have read := (weights_lookup A R N v p hp).eqTrans (entry_congr (.eqRefl v) (row_column_at A R N N p j hj tag))
  exact folded.eqTrans ((GaussianRationalMatrixFiniteSums.sum_delta reader R p C hp).eqTrans
    (by rw [reader_at]; exact recode_congr read))

theorem full_reduced_witness (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hFull : Γ ⊢[PRAAx] rank A R N ≐ N) (hv : Γ ⊢[PRAAx] length v ≐ N) : Γ ⊢[PRAAx]
    witness (finalMatrix A R N) R N (weights A R N v) v := by
  have hMarked := count_full_marked (finalHistory A R N) N hFull
  have hMs : Γ.map Fm.shift ⊢[PRAAx] allMarked (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hMarked.shift
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  refine .andI (GaussianRationalEliminationLoop.matrix_shape A R N N hA) (.andI (weights_length _ _ _ _) (.andI hv ?_))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have col := combination_coordinate (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v) (var 0)
    hAs.wk hMs.wk Prf.hyp0
  have actual := (GaussianRationalRowSpan.combination_lookup (Γ := Δ) _ _ _ _ _ Prf.hyp0).eqTrans col
  have canon := GaussianRationalRowSpan.combination_canonical (Γ := Δ)
    (finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R) (Syn.shift N)
    (weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v)) (var 0) Prf.hyp0
  simpa [Δ,Syn.shift] using GaussianRationalValueEquality.equal_values_of_recode_equal _ _
    (((GaussianTranslatedNonconstant.recode_eq _ canon).eqTrans actual).eqSymm)

theorem actual_full_reduced_span_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ rank (var 0) (var 1) (var 2) ≐ var 2 ⟶ length (var 3) ≐ var 2 ⟶
      witness (finalMatrix (var 0) (var 1) (var 2)) (var 1) (var 2) (weights (var 0) (var 1) (var 2) (var 3)) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (full_reduced_witness _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalFullReducedSpan
