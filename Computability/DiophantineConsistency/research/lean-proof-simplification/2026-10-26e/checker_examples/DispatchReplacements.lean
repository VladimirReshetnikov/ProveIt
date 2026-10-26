import DiophantineConsistency.AnnotatedBoundLocal

/-!
Authored candidate, not compiler-checked. This is a proof-level rewrite only:
threshold-based executable dispatch and its invalid-tag rejection stay intact.
-/
namespace CheckerRefactor

/-- Ordered threshold dispatch agrees with the frozen eight-tag specification.
No boundedness assumption on the untrusted natural tag is introduced. -/
theorem threshold_dispatch_eq {α : Type} (tag : Nat)
    (atomic bottom binary unary invalid : α) :
    (if tag - 1 = 0 then atomic
     else if tag = 2 then bottom
     else if tag - 5 = 0 then binary
     else if tag - 7 = 0 then unary
     else invalid) =
    (if tag = 0 then atomic
     else if tag = 1 then atomic
     else if tag = 2 then bottom
     else if tag = 3 ∨ tag = 4 ∨ tag = 5 then binary
     else if tag = 6 ∨ tag = 7 then unary
     else invalid) := by
  split_ifs <;> first | rfl | omega

end CheckerRefactor

namespace DiophantineConsistency.AnnotatedBoundLocal
open AnnotatedRename (Row rowCode decodeRow_rowCode)
open AnnotatedCodeArithmetic (listCode)
open AnnotatedBound

-- Replacement body of AnnotatedBoundLocal.localCheck_correct.
example (r : Row) (seen : List Row) :
    localCheck (rowCode r) (listCode (seen.map rowCode)) = 1 ↔ valid r seen = true := by
  simp only [localCheck, decodeRow_rowCode, CheckerRefactor.threshold_dispatch_eq, valid]
  split_ifs <;>
    simp_all only [atomicCheck_correct, bottomCheck, decodeRow_rowCode,
      AnnotatedRenameLocal.truth_eq_one, binaryCheck_correct, unaryCheck_correct,
      Nat.zero_eq_one, Bool.false_eq_true]

end DiophantineConsistency.AnnotatedBoundLocal

namespace DiophantineConsistency.AnnotatedRenameLocal
open AnnotatedRename (Row rowCode decodeRow_rowCode)
open AnnotatedCodeArithmetic (listCode)

-- Replacement body of AnnotatedRenameLocal.localCheck_correct.
example (mode k : Nat) (r : Row) (seen : List Row) :
    localCheck mode k (rowCode r) (listCode (seen.map rowCode)) = 1 ↔
      r.valid mode k seen = true := by
  simp only [localCheck, decodeRow_rowCode, CheckerRefactor.threshold_dispatch_eq, Row.valid]
  split_ifs <;>
    simp_all only [atomicCheck_correct, bottomCheck, decodeRow_rowCode,
      truth_eq_one, binaryCheck_correct, unaryCheck_correct,
      Nat.zero_eq_one, Bool.false_eq_true]

end DiophantineConsistency.AnnotatedRenameLocal
