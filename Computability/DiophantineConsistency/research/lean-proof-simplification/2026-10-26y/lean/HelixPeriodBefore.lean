import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace ProofSimplificationBefore
theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  induction t using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
      have hh := hhelix x ((n : ℤ)+1)
      rw [add_sub_cancel_right] at hh
      calc
        T x ((n : ℤ)+1) = T (x+w) n := hh.symm
        _ = T ((x+w)+w*n) 0 := ih _
        _ = T (x+w*((n : ℤ)+1)) 0 := by congr 1; ring
  | pred n ih =>
      have hh := hhelix (x-w) (-(n : ℤ))
      rw [sub_add_cancel] at hh
      calc
        T x (-(n : ℤ)-1) = T (x-w) (-(n : ℤ)) := hh
        _ = T ((x-w)+w*(-(n : ℤ))) 0 := ih _
        _ = T (x+w*(-(n : ℤ)-1)) 0 := by congr 1; ring


#print axioms row_zero_of_helix
end ProofSimplificationBefore
