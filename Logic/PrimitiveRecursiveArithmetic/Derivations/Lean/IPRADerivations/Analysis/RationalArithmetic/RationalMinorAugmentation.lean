import IPRADerivations.Analysis.RationalArithmetic.RationalMinorMaskExtension
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual larger minors at the first free column

Adjoin the first unselected column and any unselected row to the bounded
maximum-minor scan's chosen masks. The resulting matrix is a square minor
of size one larger than the actual rank. Its cleared determinant vanishes
by the same bounded scan that chose the original minor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMinorAugmentation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB inst2_sgB)
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalSelectedMinors (count indices index normalized normalized_lookup)
open RationalMaximalMinors (bestRow bestColumn rank rowSize columnSize clearedValue best_valid larger_minor_zero)
open RationalMinorFreeColumn (free free_column_spec free_least)
open RationalMinorMaskExtension (insert insert_bound insert_count inserted_listed)
open RationalSupMetric (coordinate normalizedList)
open RationalIntegerNormalization (normalize)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalHorner (qzero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def extendedRow (P d i : PTm n) : PTm n := insert (length P) (bestRow P d) i
def extendedColumn (P d : PTm n) : PTm n := insert d (bestColumn P d) (free P d)

@[simp] theorem subst_extendedRow {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (extendedRow P d i) = extendedRow (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by
  simp [extendedRow]

@[simp] theorem subst_extendedColumn {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (extendedColumn P d) = extendedColumn (Syn.subst σ P) (Syn.subst σ d) := by
  simp [extendedColumn]

theorem extended_row_size (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ zero) :
    Γ ⊢[PRAAx] rowSize P (extendedRow P d i) ≐ succ (rank P d) :=
  insert_count (length P) (bestRow P d) i hi hb

theorem extended_column_size (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] columnSize d (extendedColumn P d) ≐ succ (rank P d) := by
  have spec := free_column_spec P d h
  exact (insert_count d (bestColumn P d) (free P d) spec.andE₁ spec.andE₂).eqTrans
    (congrSucc (best_valid P d).andE₁.eqSymm)

theorem extended_minor_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hi : Γ ⊢[PRAAx] lt i (length P)) (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ zero) :
    Γ ⊢[PRAAx] clearedValue P d (extendedRow P d i) (extendedColumn P d) ≐ qzero := by
  have hr := extended_row_size P d i hi hb
  have hc := extended_column_size P d h
  exact larger_minor_zero P d _ _
    (insert_bound (length P) (bestRow P d) i) (insert_bound d (bestColumn P d) (free P d))
    (hr.eqTrans hc.eqSymm) (lt_congr (.eqRefl _) hr.eqSymm (le_refl _))

theorem free_prefix_count (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] count (free P d) (bestColumn P d) ≐ free P d := by
  have s := sum_congr_bounded (Γ := Γ) (sgB bitBody) (one : PTm 2) (bestColumn P d) (bestColumn P d) (free P d)
  refine (s (.allI (.impI ?_))).eqTrans (AnalyticNumberTheory.SumPhi.sum_ones _ _)
  let P' := Syn.shift P
  let d' := Syn.shift d
  let Δ := lt (var 0) (free P' d') :: Γ.map Fm.shift
  have valid : Δ ⊢[PRAAx] lt (rank P' d') d' := by
    simpa only [Δ,P',d',Fm.shift,subst_lt,RationalMaximalMinors.subst_rank,Syn.shift] using h.shift.wk
  have hit := free_least P' d' (var 0) valid (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (free P' d'))
  have e := (congrMonus (.eqRefl (one : PTm (n+1))) (congrMonus (.eqRefl _) hit)).eqTrans (Signum.sg_succ zero)
  rw [inst2_sgB,bit_body_at]
  simpa [Δ,P',d',Signum.sg,Syn.shift,inst2,one] using e

theorem extended_row_position (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    lt (count i (bestRow P d)) (rowSize P (extendedRow P d i)) ⋏
      index (length P) (extendedRow P d i) (count i (bestRow P d)) ≐ i :=
  inserted_listed (length P) (bestRow P d) i hi

theorem extended_column_position (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) : Γ ⊢[PRAAx]
    lt (free P d) (columnSize d (extendedColumn P d)) ⋏ index d (extendedColumn P d) (free P d) ≐ free P d := by
  have listed := inserted_listed d (bestColumn P d) (free P d) (free_column_spec P d h).andE₁
  have countFree := free_prefix_count P d h
  exact .andI (lt_congr countFree (.eqRefl _) listed.andE₁)
    ((entry_congr (.eqRefl (indices d (extendedColumn P d))) countFree.eqSymm).eqTrans listed.andE₂)

theorem extended_inserted_cell (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    cell (normalized P d (extendedRow P d i) (extendedColumn P d)) (count i (bestRow P d)) (free P d) ≐
      normalize (coordinate (entry (normalizedList P d) i) (free P d)) one := by
  have rows := extended_row_position P d i hi
  have columns := extended_column_position P d h
  refine (normalized_lookup P d (extendedRow P d i) (extendedColumn P d) _ _ rows.andE₁ columns.andE₁).eqTrans ?_
  ipra_congr (normalize (coordinate (entry (var 0) (var 1)) (var 2)) one : PTm 3) with
    [.eqRefl (normalizedList P d), rows.andE₂, columns.andE₂] using [RationalSupMetric.coordinate, one, ZT.subst]

theorem actual_extended_minor_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      bit (bestRow (var 0) (var 1)) (var 2) ≐ zero ⟶
      rowSize (var 0) (extendedRow (var 0) (var 1) (var 2)) ≐ succ (rank (var 0) (var 1)) ⋏
      columnSize (var 1) (extendedColumn (var 0) (var 1)) ≐ succ (rank (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (.andI (extended_row_size _ _ _ Prf.hyp1 Prf.hyp0)
    (extended_column_size _ _ (Prf.hyp1 : _ ⊢[PRAAx] _).wk)))))

theorem actual_extended_minor_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      bit (bestRow (var 0) (var 1)) (var 2) ≐ zero ⟶
      clearedValue (var 0) (var 1) (extendedRow (var 0) (var 1) (var 2))
        (extendedColumn (var 0) (var 1)) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (.impI (extended_minor_zero _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_extended_free_column_position_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (rank (var 0) (var 1)) (var 1) ⟶
      lt (free (var 0) (var 1)) (columnSize (var 1) (extendedColumn (var 0) (var 1))) ⋏
      index (var 1) (extendedColumn (var 0) (var 1)) (free (var 0) (var 1)) ≐ free (var 0) (var 1)) :=
  closeUniv 2 (.impI (extended_column_position _ _ Prf.hyp0))

theorem actual_extended_inserted_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      cell (normalized (var 0) (var 1) (extendedRow (var 0) (var 1) (var 2)) (extendedColumn (var 0) (var 1)))
        (count (var 2) (bestRow (var 0) (var 1))) (free (var 0) (var 1)) ≐
      normalize (coordinate (entry (normalizedList (var 0) (var 1)) (var 2)) (free (var 0) (var 1))) one) :=
  closeUniv 3 (.impI (.impI (extended_inserted_cell _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalMinorAugmentation
