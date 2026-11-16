module
public import M6Data
public import RowBridge
@[expose] public section
namespace PalomarPA
open M6.Arithmetic
open M6.Arithmetic.PA
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def actualRowSpec (p : WorkingState × Bool) : RowSpec :=
  let a := row p.1 p.2
  (p.1.val,p.2.toNat,a.write.toNat,StepFormula.controlCode a.next,a.right)
def activeRows := StepFormula.rows.filter (fun p => decide (active p.1))
/-- Kernel equality against the actual M6 row function, not a hash assertion. -/
theorem m6Rows_exact : m6Rows = activeRows.map actualRowSpec := by decide +kernel

theorem disjoinRows_exact (rs : List (WorkingState × Bool)) :
    (disjoinRows (rs.map actualRowSpec)).toFoundation = StepFormula.disjoin rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨q,b⟩
    change FFL.FirstOrder.Semiformula.or _ _ = FFL.FirstOrder.Semiformula.or _ _
    congr 1
    · exact rowFormula_exact q b

theorem m6Step_exact : m6Step.toFoundation = StepFormula.disjoin activeRows := by
  rw [m6Step,m6Rows_exact,disjoinRows_exact]
#print axioms m6Rows_exact
#print axioms m6Step_exact
end PalomarPA
