import IPRADerivations.Analysis.RationalCofactorMinorBounds
import IPRADerivations.Analysis.RationalMinorOrderTransport
import IPRADerivations.Analysis.RationalMinorMaskReconstruction
import IPRADerivations.Foundations.RuntimePermutationInsertion
import IPRADerivations.Core.CongruenceTactic

/-!
# Ordered columns of the actual cofactor minors

For an actually retained column of the enlarged mask, the cofactor mask
is exactly the mask before restoring that one column. The numerical skip
map therefore identifies every smaller column with the corresponding
larger column, and reads the same cleared matrix entry.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorColumnOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (slot)
open LeanProofs.IPRA.Foundations.RuntimePermutationInsertion (slot_congr)
open RationalSubtupleSpan (bit)
open RationalSelectedMinors (count index normalized normalized_lookup)
open RationalMinorFreeColumn (free free_column_spec)
open RationalMinorMaskExtension (insert insert_bound prefix_count_before)
open RationalMinorMaskDeletion (erase erased_bit)
open RationalMinorMaskReconstruction (restore_erased bit_congr)
open RationalMinorOrderTransport (original_slot)
open RationalMinorAugmentation (extendedColumn)
open RationalMaximalMinors (bestRow bestColumn rank)
open RationalCofactorMinorBounds (columnMask free_mask other_mask column_count_congr)
open RationalSupMetric (coordinate normalizedList)
open RationalIntegerNormalization (normalize)
open GaussianPolynomialDeterminantTerms (cell)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem insert_congr (N : PTm n) {R S j k : PTm n} (h : Γ ⊢[PRAAx] R ≐ S) (hj : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] insert N R j ≐ insert N S k := by
  ipra_congr (insert (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl N, h, hj]

theorem cofactor_omits (P d j : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d) :
    Γ ⊢[PRAAx] bit (columnMask P d j) j ≐ zero := by
  refine .orE (eq_or_ne j (free P d)) ?_ ?_
  · exact (bit_congr (free_mask P d j Prf.hyp0) Prf.hyp0).eqTrans (free_column_spec P d h.wk).andE₂
  · exact (bit_congr (other_mask P d j Prf.hyp0) (.eqRefl j)).eqTrans (erased_bit d (extendedColumn P d) j hj.wk)

theorem restore_cofactor (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) :
    Γ ⊢[PRAAx] insert d (columnMask P d j) j ≐ extendedColumn P d := by
  refine .orE (eq_or_ne j (free P d)) ?_ ?_
  · exact insert_congr d (free_mask P d j Prf.hyp0) Prf.hyp0
  · exact (insert_congr d (other_mask P d j Prf.hyp0) (.eqRefl j)).eqTrans
      (restore_erased d (extendedColumn P d) j (insert_bound d (bestColumn P d) (free P d)) hj.wk hs.wk)

theorem omitted_prefix (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) :
    Γ ⊢[PRAAx] count j (extendedColumn P d) ≐ count j (columnMask P d j) :=
  (column_count_congr j (restore_cofactor P d j hj hs)).eqSymm.eqTrans
    (prefix_count_before d (columnMask P d j) j j (le_of_lt hj) (le_refl j))

theorem index_congr (d : PTm n) {R S j k : PTm n} (h : Γ ⊢[PRAAx] R ≐ S) (hj : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] index d R j ≐ index d S k := by
  ipra_congr (index (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl d, h, hj]

theorem cofactor_slot (P d j r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) (hr : Γ ⊢[PRAAx] lt r (count d (columnMask P d j))) :
    Γ ⊢[PRAAx] lt (slot (count j (extendedColumn P d)) r) (count d (extendedColumn P d)) ⋏
      index d (extendedColumn P d) (slot (count j (extendedColumn P d)) r) ≐ index d (columnMask P d j) r := by
  let M := columnMask P d j
  have selected := original_slot d M j r hr (cofactor_omits P d j h hj)
  have restored := restore_cofactor P d j hj hs
  have positions := slot_congr (omitted_prefix P d j hj hs).eqSymm (.eqRefl r)
  exact .andI (lt_congr positions (column_count_congr d restored) selected.andE₁)
    ((index_congr d restored positions).eqSymm.eqTrans selected.andE₂)

private theorem cleared_entry_congr (A i : PTm n) {j k : PTm n} (h : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] normalize (coordinate (entry A i) j) one ≐ normalize (coordinate (entry A i) k) one := by
  ipra_congr (normalize (coordinate (entry (var 0) (var 1)) (var 2)) one : PTm 3) with
    [.eqRefl A, .eqRefl i, h] using [RationalSupMetric.coordinate, one, ZT.subst]

theorem cofactor_cell (P d j i r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) (hi : Γ ⊢[PRAAx] lt i (rank P d))
    (hr : Γ ⊢[PRAAx] lt r (count d (columnMask P d j))) :
    Γ ⊢[PRAAx] cell (normalized P d (bestRow P d) (columnMask P d j)) i r ≐
      cell (normalized P d (bestRow P d) (extendedColumn P d)) i (slot (count j (extendedColumn P d)) r) := by
  have atSlot := cofactor_slot P d j r h hj hs hr
  have small := normalized_lookup P d (bestRow P d) (columnMask P d j) i r hi hr
  have big := normalized_lookup P d (bestRow P d) (extendedColumn P d) i _ hi atSlot.andE₁
  exact small.eqTrans ((cleared_entry_congr (normalizedList P d) (index (length P) (bestRow P d) i) atSlot.andE₂.eqSymm).eqTrans big.eqSymm)

theorem actual_cofactor_restores_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ bit (extendedColumn (var 0) (var 1)) (var 2) ≐ one ⟶
      insert (var 1) (columnMask (var 0) (var 1) (var 2)) (var 2) ≐ extendedColumn (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (restore_cofactor _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_cofactor_column_entry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (var 1) ⟶ bit (extendedColumn (var 0) (var 1)) (var 2) ≐ one ⟶
      lt (var 3) (rank (var 0) (var 1)) ⟶ lt (var 4) (count (var 1) (columnMask (var 0) (var 1) (var 2))) ⟶
      cell (normalized (var 0) (var 1) (bestRow (var 0) (var 1)) (columnMask (var 0) (var 1) (var 2))) (var 3) (var 4) ≐
        cell (normalized (var 0) (var 1) (bestRow (var 0) (var 1)) (extendedColumn (var 0) (var 1))) (var 3)
          (slot (count (var 2) (extendedColumn (var 0) (var 1))) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (cofactor_cell _ _ _ _ _ (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.RationalCofactorColumnOrder
