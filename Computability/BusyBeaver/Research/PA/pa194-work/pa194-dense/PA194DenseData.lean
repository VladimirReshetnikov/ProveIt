import PA194AllTape
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LocalQuotient

def label (q : Nat) : Nat := labels[q]?.getD 254

def denseRowGood (r : Row) : Bool := decide (r.state < 194) && decide (r.target ≤ 194)

def denseControlGood (q : Nat) : Bool :=
  (lookup dense q false).isSome && (lookup dense q true).isSome

theorem dense_control_certificate : dense.all denseRowGood = true ∧
    (List.range 194).all denseControlGood = true ∧ label 0 = 74 ∧ label 194 = 254 := by
  decide +kernel

#print axioms dense_control_certificate
end PA194LocalQuotient
