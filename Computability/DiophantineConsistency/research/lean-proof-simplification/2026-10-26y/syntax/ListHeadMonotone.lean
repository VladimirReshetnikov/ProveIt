import Mathlib.Algebra.Order.Monoid.Defs

namespace ProofSimplification.ListHead
variable {R : Type*} [AddCommMonoid R] [One R] [Preorder R] [IsOrderedAddMonoid R]
    (pair : R → R → R) (left right head : R → R)

def cons (a b : R) := pair a b + 1

/-- Abstract check of the exact consumer proof using its existing interface. -/
theorem head_le
    (zero_or_cons : ∀ c, c = 0 ∨ c = cons pair (left c) (right c))
    (head_zero : head 0 = 0)
    (head_cons : ∀ a b, head (cons pair a b) = a + 1)
    (left_le_pair : ∀ a b, a ≤ pair a b) (c : R) : head c ≤ c := by
  rcases zero_or_cons c with hz | hc
  · rw [hz, head_zero]
  · rw [hc, head_cons]
    exact add_le_add (left_le_pair _ _) (le_refl 1)

#print axioms head_le
end ProofSimplification.ListHead
