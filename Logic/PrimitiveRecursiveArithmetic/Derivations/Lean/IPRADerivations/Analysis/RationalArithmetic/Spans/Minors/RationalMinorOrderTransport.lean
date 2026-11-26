import IPRADerivations.Analysis.RationalArithmetic.Spans.Minors.RationalMinorAugmentation
import IPRADerivations.Foundations.RuntimePermutationDeletion

/-!
# Original selected labels in the augmented minor

The skip map used by numerical permutation deletion also embeds the exact
old selected coordinates into the enlarged sorted masks. This identifies the
old rows and columns in the order used by a bounded determinant expansion.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMinorOrderTransport

open_ipra
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank_mono rank_lt_of_kept)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (slot slot_before slot_after)
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalSelectedMinors (count indices index index_selected normalized normalized_lookup)
open RationalMinorMaskExtension (insert index_rank retained_before retained_after)
open RationalMinorFreeColumn (free free_column_spec)
open RationalMaximalMinors (bestRow bestColumn rank rowSize columnSize)
open RationalMinorAugmentation (extendedRow extendedColumn free_prefix_count)
open RationalSupMetric (coordinate normalizedList)
open RationalIntegerNormalization (normalize)
open GaussianPolynomialDeterminantTerms (cell)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem index_congr (N M : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] index N M a ≐ index N M b :=
  entry_congr (.eqRefl (indices N M)) h

theorem original_slot (N M c r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count N M)) (hc : Γ ⊢[PRAAx] bit M c ≐ zero) :
    Γ ⊢[PRAAx] lt (slot (count c M) r) (count N (insert N M c)) ⋏
      index N (insert N M c) (slot (count c M) r) ≐ index N M r := by
  let i := index N M r
  have present : Γ ⊢[PRAAx] neg (bit M i ≐ zero) := index_selected N M r hr
  have whereRank : Γ ⊢[PRAAx] count i M ≐ r := index_rank N M r hr
  refine .orE (lt_or_le i c) ?_ ?_
  · have kept : (lt i c) :: Γ ⊢[PRAAx] neg (inst2 bitBody i M ≐ zero) := by simpa only [bit_body_at] using present.wk
    have before : (lt i c) :: Γ ⊢[PRAAx] lt r (count c M) :=
      lt_congr whereRank.wk (.eqRefl _) (rank_lt_of_kept bitBody kept Prf.hyp0)
    have position := slot_before (count c M) r before
    have retained := retained_before N M c r hr.wk (Prf.hyp0 : lt i c :: Γ ⊢[PRAAx] lt i c)
    exact .andI (lt_congr position.eqSymm (.eqRefl _) retained.andE₁)
      ((index_congr N (insert N M c) position).eqTrans retained.andE₂)
  · refine .orE (lt_or_eq_of_le (Prf.hyp0 : le c i :: Γ ⊢[PRAAx] le c i)) ?_ ?_
    · have after : (lt c i) :: le c i :: Γ ⊢[PRAAx] le (count c M) r :=
        le_congr (.eqRefl _) whereRank.wk.wk (rank_mono bitBody Prf.hyp1 M)
      have position := slot_after (count c M) r after
      have retained := retained_after N M c r hr.wk.wk hc.wk.wk (Prf.hyp0 : lt c i :: le c i :: Γ ⊢[PRAAx] lt c i)
      exact .andI (lt_congr position.eqSymm (.eqRefl _) retained.andE₁)
        ((index_congr N (insert N M c) position).eqTrans retained.andE₂)
    · apply Prf.botE
      have e : (c ≐ i) :: le c i :: Γ ⊢[PRAAx] bit M c ≐ bit M i := by
        ipra_congr (bit (var 0) (var 1) : PTm 2) with [.eqRefl M, Prf.hyp0]
      exact .impE present.wk.wk (e.eqSymm.eqTrans hc.wk.wk)

theorem original_row_slot (P d i r : PTm n) (hr : Γ ⊢[PRAAx] lt r (rank P d))
    (hi : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ zero) : Γ ⊢[PRAAx]
    lt (slot (count i (bestRow P d)) r) (rowSize P (extendedRow P d i)) ⋏
      index (length P) (extendedRow P d i) (slot (count i (bestRow P d)) r) ≐ index (length P) (bestRow P d) r :=
  original_slot (length P) (bestRow P d) i r hr hi

theorem original_column_slot (P d r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hr : Γ ⊢[PRAAx] lt r (columnSize d (bestColumn P d))) : Γ ⊢[PRAAx]
    lt (slot (free P d) r) (columnSize d (extendedColumn P d)) ⋏
      index d (extendedColumn P d) (slot (free P d) r) ≐ index d (bestColumn P d) r := by
  have original := original_slot d (bestColumn P d) (free P d) r hr (free_column_spec P d h).andE₂
  have position : Γ ⊢[PRAAx] slot (count (free P d) (bestColumn P d)) r ≐ slot (free P d) r := by
    ipra_congr (slot (var 0) (var 1) : PTm 2) with [free_prefix_count P d h, .eqRefl r] using [slot, one]
  exact .andI (lt_congr position (.eqRefl _) original.andE₁)
    ((index_congr d (extendedColumn P d) position.eqSymm).eqTrans original.andE₂)

private theorem cleared_entry_congr (Q : PTm n) {i i' j j' : PTm n}
    (hi : Γ ⊢[PRAAx] i ≐ i') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    normalize (coordinate (entry Q i) j) one ≐ normalize (coordinate (entry Q i') j') one := by
  ipra_congr (normalize (coordinate (entry (var 0) (var 1)) (var 2)) one : PTm 3) with
    [.eqRefl Q, hi, hj] using [RationalSupMetric.coordinate, one, ZT.subst]

theorem retained_cell (P d i r s : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hr : Γ ⊢[PRAAx] lt r (rank P d)) (hs : Γ ⊢[PRAAx] lt s (columnSize d (bestColumn P d)))
    (hi : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ zero) : Γ ⊢[PRAAx]
    cell (normalized P d (extendedRow P d i) (extendedColumn P d)) (slot (count i (bestRow P d)) r) (slot (free P d) s) ≐
      cell (normalized P d (bestRow P d) (bestColumn P d)) r s := by
  have row := original_row_slot P d i r hr hi
  have col := original_column_slot P d s h hs
  have oldCell := normalized_lookup P d (bestRow P d) (bestColumn P d) r s hr hs
  have newCell := normalized_lookup P d (extendedRow P d i) (extendedColumn P d)
    (slot (count i (bestRow P d)) r) (slot (free P d) s) row.andE₁ col.andE₁
  exact newCell.eqTrans ((cleared_entry_congr (normalizedList P d) row.andE₂ col.andE₂).eqTrans oldCell.eqSymm)

theorem actual_retained_minor_slot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (count (var 0) (var 1)) ⟶ bit (var 1) (var 2) ≐ zero ⟶
      lt (slot (count (var 2) (var 1)) (var 3)) (count (var 0) (insert (var 0) (var 1) (var 2))) ⋏
      index (var 0) (insert (var 0) (var 1) (var 2)) (slot (count (var 2) (var 1)) (var 3)) ≐
        index (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (original_slot _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_retained_column_slot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (columnSize (var 1) (bestColumn (var 0) (var 1))) ⟶
      lt (slot (free (var 0) (var 1)) (var 2)) (columnSize (var 1) (extendedColumn (var 0) (var 1))) ⋏
      index (var 1) (extendedColumn (var 0) (var 1)) (slot (free (var 0) (var 1)) (var 2)) ≐
        index (var 1) (bestColumn (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_column_slot _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_retained_minor_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 3) (rank (var 0) (var 1)) ⟶
      lt (var 4) (columnSize (var 1) (bestColumn (var 0) (var 1))) ⟶ bit (bestRow (var 0) (var 1)) (var 2) ≐ zero ⟶
      cell (normalized (var 0) (var 1) (extendedRow (var 0) (var 1) (var 2)) (extendedColumn (var 0) (var 1)))
        (slot (count (var 2) (bestRow (var 0) (var 1))) (var 3)) (slot (free (var 0) (var 1)) (var 4)) ≐
      cell (normalized (var 0) (var 1) (bestRow (var 0) (var 1)) (bestColumn (var 0) (var 1))) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (retained_cell _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.RationalMinorOrderTransport
