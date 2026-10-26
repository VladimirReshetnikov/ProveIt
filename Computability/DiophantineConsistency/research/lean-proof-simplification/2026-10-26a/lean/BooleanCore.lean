import Init

namespace DiophantineConsistency.ProofSimplification

/-- A Boolean-valued natural classifier is determined by its accepting case. -/
theorem eq_truth_of_boolean (n : Nat) (b : Bool) (hn : n = 0 ∨ n = 1)
    (haccept : n = 1 ↔ b = true) : n = (if b then 1 else 0) := by
  cases b <;> simp_all

#print axioms eq_truth_of_boolean

end DiophantineConsistency.ProofSimplification
