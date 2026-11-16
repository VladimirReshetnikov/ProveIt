import PA194AllTape
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LocalQuotient

/-- A native source control is either the halt label or has a table row. -/
def knownControl (q : Nat) : Bool := parent.any (fun row => row.state == q)
def validControl (q : Nat) : Prop := q = 254 ∨ knownControl q = true

def controlGood (row : Row) : Bool :=
  (lookup parent row.state false).isSome && (lookup parent row.state true).isSome &&
    (row.target == 254 || knownControl row.target)

theorem finite_controls : parent.all controlGood = true ∧ knownControl 74 = true ∧
    lookup folded 254 false = none ∧ lookup folded 254 true = none ∧ project 254 = 254 := by
  decide +kernel


#print axioms finite_controls
end PA194LocalQuotient
