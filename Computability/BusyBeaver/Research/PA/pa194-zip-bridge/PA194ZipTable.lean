import PA194ZipBridge
import PA194Literal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ZipBridge
open PA194LocalQuotient

def rowTriple (r : Row) : Bool × Bool × Nat := (r.write, r.right, r.target)

/-- Direct kernel comparison of all 388 dense rows against the generated
literal transition function from the separately pinned machine table. -/
theorem all_literal_rows : ∀ (q : Fin 194) (b : Bool),
    (lookup dense q.val b).map rowTriple = some (PA194.Literal.transition q.val b) := by
  decide +kernel

#print axioms all_literal_rows
end PA194ZipBridge
