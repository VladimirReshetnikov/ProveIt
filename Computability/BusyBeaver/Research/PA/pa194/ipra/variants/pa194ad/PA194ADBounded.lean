import PA194ADStep
import PA194Bounded
set_option autoImplicit false
namespace PA194ADTable

theorem primary_next (c : Conf) : next PA194Rows.rows c = PA194Bounded.next c := rfl

theorem primary_run (n : Nat) : run PA194Rows.rows (0,0,0) n = PA194Bounded.run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change next PA194Rows.rows (run PA194Rows.rows (0,0,0) n) =
      PA194Bounded.next (PA194Bounded.run n)
    rw [primary_next, ih]

#print axioms primary_next
#print axioms primary_run
end PA194ADTable
