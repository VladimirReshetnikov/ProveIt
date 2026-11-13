module
public import PA196.Palomar.Data
public import PA196.Palomar.RowBridge
@[expose] public section
namespace PalomarPA.PA196
open PA196.Arithmetic.Machine.Exact
open PA196.Arithmetic.Machine.Exact.PA
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def actualRowSpec (p : WorkingState × Bool) : RowSpec :=
  let a := row p.1 p.2
  (p.1.val,p.2.toNat,a.write.toNat,StepFormula.controlCode a.next,a.right)
def activeRows := StepFormula.rows
/-- Kernel equality against the exact PA196 literal row function, not a hash assertion. -/
theorem pa196Rows_exact : pa196Rows = activeRows.map actualRowSpec := by decide +kernel

theorem disjoinRows_exact (rs : List (WorkingState × Bool)) :
    (disjoinRows (rs.map actualRowSpec)).toFoundation = StepFormula.disjoin rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨q,b⟩
    change FFL.FirstOrder.Semiformula.or _ _ = FFL.FirstOrder.Semiformula.or _ _
    congr 1
    · exact rowFormula_exact q b

theorem pa196Step_exact : pa196Step.toFoundation = StepFormula.disjoin activeRows := by
  rw [pa196Step,pa196Rows_exact,disjoinRows_exact]
#print axioms pa196Rows_exact
#print axioms pa196Step_exact
end PalomarPA.PA196
