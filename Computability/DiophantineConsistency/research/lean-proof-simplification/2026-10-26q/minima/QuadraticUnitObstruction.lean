import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace QuadraticUnitObstruction

/-- One residue obstruction covers every discriminant one below a square. -/
theorem square_sub_one_norm_ne_neg_one (A X Y : ℤ) :
    X ^ 2 - (A ^ 2 - 1) * Y ^ 2 ≠ -1 := by
  intro he
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) he
  push_cast at hm
  have bad : ∀ A X Y : ZMod 4, X ^ 2 - (A ^ 2 - 1) * Y ^ 2 ≠ -1 := by decide
  exact bad _ _ _ hm

-- Exact four current public statements, with new specialization proofs.
theorem strong_ne_neg_one (a f t : ℤ) :
    f ^ 2 - ((a + 2) ^ 2 - 1) * t ^ 2 ≠ -1 :=
  square_sub_one_norm_ne_neg_one (a + 2) f t

theorem square_aux_ne_neg_one (t h y : ℤ) :
    t ^ 2 * (h ^ 2 - y ^ 2) + y ^ 2 ≠ -1 := by
  convert square_sub_one_norm_ne_neg_one t (t * h) y using 1 <;> ring

theorem main_norm_ne_neg_one (a x y : ℤ) :
    x ^ 2 - (a ^ 2 + 4 * a + 3) * y ^ 2 ≠ -1 := by
  convert square_sub_one_norm_ne_neg_one (a + 2) x y using 1 <;> ring

def auxiliary {R : Type*} [CommRing R] (U V e : R) : R :=
  U * V ^ 2 - (U - 1) * (V + e) ^ 2

theorem square_auxiliary_ne_neg_one (I V e : ℤ) : auxiliary (I ^ 2) V e ≠ -1 := by
  simpa only [auxiliary, mul_pow] using square_sub_one_norm_ne_neg_one I (I * V) (V + e)

#print axioms square_sub_one_norm_ne_neg_one
#print axioms strong_ne_neg_one
#print axioms square_aux_ne_neg_one
#print axioms main_norm_ne_neg_one
#print axioms square_auxiliary_ne_neg_one
end QuadraticUnitObstruction
