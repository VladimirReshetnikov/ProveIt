import DiophantineConsistency.AnnotatedBoundScan

/-!
Authored candidate, not a verified patch. The proposed interface strengthens
existing soundness/completeness plus Booleanity to an exact numeric equality.
All executable localCheck and step definitions are preserved.
-/
namespace CheckerRefactor
open DiophantineConsistency.AnnotatedRenameLocal (truth)

/-- Upgrade a zero/one classifier's truth specification to exact equality. -/
theorem eq_truth_of_boolean (value : Nat) (b : Bool)
    (boolean : value = 0 ∨ value = 1) (correct : value = 1 ↔ b = true) :
    value = truth b := by
  cases b with
  | false =>
    rcases boolean with h | h
    · exact h
    · have impossible := correct.mp h
      cases impossible
  | true => exact correct.mpr rfl

end CheckerRefactor

namespace DiophantineConsistency.AnnotatedBoundLocal
open AnnotatedRename (Row rowCode tableCode)
open AnnotatedRenameLocal (truth)

/-- Proposed reusable public lemma; this is stronger than _correct alone. -/
theorem localCheck_eq_truth_candidate (r : Row) (seen : List Row) :
    localCheck (rowCode r) (tableCode seen) = truth (AnnotatedBound.valid r seen) :=
  CheckerRefactor.eq_truth_of_boolean _ _ (localCheck_boolean _ _)
    (localCheck_correct r seen)

end DiophantineConsistency.AnnotatedBoundLocal

namespace DiophantineConsistency.AnnotatedBoundScan
open AnnotatedRename (Row tableCode)
open AnnotatedCodeArithmetic (listCode)

-- Replacement of step_cons, keeping its original statement.
example (r : Row) (rows seen : List Row) :
    step (Nat.pair (tableCode (r :: rows)) (tableCode seen)) =
      if AnnotatedBound.valid r seen then
        Nat.pair (tableCode rows) (tableCode (r :: seen)) else 0 := by
  have hl := AnnotatedBoundLocal.localCheck_eq_truth_candidate r seen
  change AnnotatedBoundLocal.localCheck (AnnotatedRename.rowCode r)
    (listCode (seen.map AnnotatedRename.rowCode)) = _ at hl
  cases hv : AnnotatedBound.valid r seen <;>
    simp [step, tableCode, List.map_cons, listCode, hl, hv, AnnotatedRenameLocal.truth]

end DiophantineConsistency.AnnotatedBoundScan

namespace DiophantineConsistency.AnnotatedRenameLocal
open AnnotatedRename (Row rowCode tableCode)

theorem localCheck_eq_truth_candidate (mode k : Nat) (r : Row) (seen : List Row) :
    localCheck mode k (rowCode r) (tableCode seen) = truth (r.valid mode k seen) :=
  CheckerRefactor.eq_truth_of_boolean _ _ (localCheck_boolean _ _ _ _)
    (localCheck_correct mode k r seen)

end DiophantineConsistency.AnnotatedRenameLocal

namespace DiophantineConsistency.AnnotatedRenameScan
open AnnotatedRename (Row tableCode)
open AnnotatedCodeArithmetic (listCode)

example (mode k : Nat) (r : Row) (rows seen : List Row) :
    step mode k (Nat.pair (tableCode (r :: rows)) (tableCode seen)) =
      if r.valid mode k seen then
        Nat.pair (tableCode rows) (tableCode (r :: seen)) else 0 := by
  have hl := AnnotatedRenameLocal.localCheck_eq_truth_candidate mode k r seen
  change AnnotatedRenameLocal.localCheck mode k (AnnotatedRename.rowCode r)
    (listCode (seen.map AnnotatedRename.rowCode)) = _ at hl
  cases hv : r.valid mode k seen <;>
    simp [step, tableCode, List.map_cons, listCode, hl, hv, AnnotatedRenameLocal.truth]

end DiophantineConsistency.AnnotatedRenameScan
