import DiophantineConsistency.ShortEquation
import Mathlib.Tactic

namespace ExistingObstructionReuse
open DiophantineConsistency

theorem square_aux_ne_neg_one (t h y : ℤ) :
    t ^ 2 * (h ^ 2 - y ^ 2) + y ^ 2 ≠ -1 := by
  convert ShortEquation.strong_ne_neg_one (t - 2) (t * h) y using 1 <;> ring

theorem main_norm_ne_neg_one (a x y : ℤ) :
    x ^ 2 - (a ^ 2 + 4 * a + 3) * y ^ 2 ≠ -1 := by
  convert ShortEquation.strong_ne_neg_one a x y using 1 <;> ring

def auxiliary {R : Type*} [CommRing R] (U V e : R) : R :=
  U * V ^ 2 - (U - 1) * (V + e) ^ 2

theorem square_auxiliary_ne_neg_one (I V e : ℤ) : auxiliary (I ^ 2) V e ≠ -1 := by
  convert ShortEquation.strong_ne_neg_one (I - 2) (I * V) (V + e) using 1 <;>
    dsimp [auxiliary] <;> ring

#print axioms square_aux_ne_neg_one
#print axioms main_norm_ne_neg_one
#print axioms square_auxiliary_ne_neg_one
end ExistingObstructionReuse
