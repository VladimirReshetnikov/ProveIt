import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic.Ring

/-!
An independent proof core for ObjectDivision.quotient_not_lt.
The carrier is not identified with Nat.  The only discreteness premise
is an explicit positive additive gap; multiplication monotonicity is unused.
-/
namespace ProofRefinements

variable {R : Type*} [CommSemiring R] [LinearOrder R]
  [CanonicallyOrderedAdd R] [IsCancelAdd R]

theorem quotient_gap_not_lt {q r q' r' n d : R}
    (h : n = q*d+r ∧ r < d) (h' : n = q'*d+r' ∧ r' < d)
    (succGap : ∀ a b : R, a < b → ∃ s, b = a+s+1) : ¬ q < q' := by
  intro hq
  obtain ⟨s, hs⟩ := succGap q q' hq
  have he : r = s*d+d+r' := add_left_cancel (a := q*d)
    (h.1.symm.trans (h'.1.trans (by rw [hs]; ring)))
  exact not_le_of_gt h.2 (he.symm ▸ (le_add_self.trans le_self_add))

#print axioms quotient_gap_not_lt

end ProofRefinements
