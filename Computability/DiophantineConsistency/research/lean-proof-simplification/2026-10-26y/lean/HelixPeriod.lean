import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Int.Basic

namespace ProofSimplificationNew

theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  have hp : Function.Periodic (fun p : ℤ × ℤ => T p.1 p.2) (w, -1) := by
    rintro ⟨a,b⟩
    simpa only [Prod.fst_add, Prod.snd_add, sub_eq_add_neg] using hhelix a b
  simpa [zsmul_eq_mul, mul_comm] using (hp.zsmul t (x,t)).symm

#print axioms row_zero_of_helix
end ProofSimplificationNew
