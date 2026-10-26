import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring

namespace ResidualPeriodicity

/-- Shearing the integer plane turns a helical translation into period one. -/
theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  have hp (y : ℤ) : Function.Periodic (fun u : ℤ => T (y-w*u) u) 1 := by
    intro u
    have he : y-w*(u+1)+w = y-w*u := by ring
    simpa only [he, add_sub_cancel_right] using (hhelix (y-w*(u+1)) (u+1)).symm
  simpa only [Int.cast_id, mul_one, mul_zero, sub_zero, add_sub_cancel_right] using
    (hp (x+w*t)).int_mul_eq t

/-- The same result is directly a period in the additive lattice Z². -/
theorem row_zero_of_helix_lattice {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  have hp : Function.Periodic (fun p : ℤ × ℤ => T p.1 p.2) (w, -1) := by
    intro p
    simpa only [Prod.fst_add, Prod.snd_add, sub_eq_add_neg] using hhelix p.1 p.2
  simpa [zsmul_eq_mul, mul_comm] using (hp.zsmul t (x,t)).symm

/-- A time-invariant proposition is one-periodic as a Prop-valued function. -/
theorem proposition_time_iff_zero (P : ℤ → Prop)
    (hstep : ∀ t, P (t+1) ↔ P t) (t : ℤ) : P t ↔ P 0 := by
  have hp : Function.Periodic P 1 := fun u => propext (hstep u)
  exact (show P t = P 0 from by simpa only [Int.cast_id, mul_one] using hp.int_mul_eq t).to_iff

/-- Decidable invariant predicates can instead be transported as Booleans. -/
theorem decidable_time_iff_zero (P : ℤ → Prop) [DecidablePred P]
    (hstep : ∀ t, P (t+1) ↔ P t) (t : ℤ) : P t ↔ P 0 := by
  have hp : Function.Periodic (fun u => decide (P u)) 1 :=
    fun u => decide_eq_decide.mpr (hstep u)
  exact decide_eq_decide.mp (by simpa only [Int.cast_id, mul_one] using hp.int_mul_eq t)

theorem original_row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
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


theorem original_proposition_time_iff_zero (P : ℤ → Prop)
    (hstep : ∀ t, P (t+1) ↔ P t) (t : ℤ) : P t ↔ P 0 := by
  induction t using Int.induction_on with
  | zero => rfl
  | succ n ih => exact (hstep (n : ℤ)).trans ih
  | pred n ih =>
      have hs := hstep (-(n : ℤ)-1)
      simp only [sub_add_cancel] at hs
      exact hs.symm.trans ih

#print axioms original_row_zero_of_helix
#print axioms original_proposition_time_iff_zero
#print axioms row_zero_of_helix_lattice
#print axioms row_zero_of_helix
#print axioms proposition_time_iff_zero
#print axioms decidable_time_iff_zero

end ResidualPeriodicity
