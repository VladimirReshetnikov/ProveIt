import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Int.Basic

namespace ProofSimplification20261026

theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  have hp : Function.Periodic (Function.uncurry T) (w, -1) := by
    intro p
    simpa only [Function.uncurry, Prod.fst_add, Prod.snd_add, sub_eq_add_neg]
      using hhelix p.1 p.2
  simpa [Function.uncurry, zsmul_eq_mul, mul_comm] using (hp.zsmul t (x,t)).symm

theorem constant_of_period_one {α : Type*} (f : ℤ → α)
    (hf : ∀ t, f (t+1) = f t) (t : ℤ) : f t = f 0 := by
  simpa using (show Function.Periodic f 1 from hf).int_mul_eq t

#print axioms row_zero_of_helix
#print axioms constant_of_period_one

end ProofSimplification20261026
