import Mathlib.Algebra.Ring.Periodic

/-! A direct replacement for the body of
`WangTiles942HelicalQuotient.row_zero_of_helix`.
The proof relies on integer multiples of a period, so negative times need no
separate induction branch. -/

namespace LeanSimplification20261026

theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  have hp : Function.Periodic (fun k : ℤ => T (x+w*k) (t-k)) 1 := by
    intro k
    simpa only [mul_add, mul_one, add_assoc, sub_add_eq_sub_sub] using
      hhelix (x+w*k) (t-k)
  simpa using (hp.int_mul t).eq.symm

#print axioms row_zero_of_helix

end LeanSimplification20261026
