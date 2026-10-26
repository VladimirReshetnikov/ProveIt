import Mathlib.Computability.RE

namespace ConstantPredicatePost01Review

/-- An abstract stand-in for the unchanged constant public set definition. -/
def refutationInputs (P : Prop) : Set ℕ := fun _ => P

/-- This formulation uses the public predicate, requiring no opened namespaces. -/
theorem refutationInputs_re (P : Prop) : REPred (refutationInputs P) := by
  classical
  exact (Computable.const (decide (refutationInputs P 0))).computablePred.to_re

#print axioms refutationInputs_re
end ConstantPredicatePost01Review
