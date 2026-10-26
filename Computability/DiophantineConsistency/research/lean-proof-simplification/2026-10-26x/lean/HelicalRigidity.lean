import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring

namespace HelicalRigidity

theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  have hp : Function.Periodic (fun s : ℤ => T (x+w*s) (t-s)) 1 := by
    intro s
    simpa only [mul_add, mul_one, ← add_assoc, sub_add_eq_sub_sub] using
      hhelix (x+w*s) (t-s)
  simpa using (hp.int_mul_eq t).symm

#print axioms row_zero_of_helix

theorem proposition_iff_zero (P : ℤ → Prop)
    (h : ∀ t, P (t+1) ↔ P t) (t : ℤ) : P t ↔ P 0 := by
  have hp : Function.Periodic P 1 := fun u => propext (h u)
  simpa only [Int.cast_id, mul_one, eq_iff_iff] using hp.int_mul_eq t

#print axioms proposition_iff_zero

end HelicalRigidity
