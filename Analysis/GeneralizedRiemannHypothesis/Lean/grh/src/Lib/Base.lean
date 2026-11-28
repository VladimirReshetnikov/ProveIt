import Lib.Speed

/-!
# The adjoint of a matrix for the Hermitian dot product

The other files of `Lib` and `New`, except `Lib.Speed`, import this file, directly or not, and
with it the speed settings of `Lib.Speed`.
-/

variable {A : Type*} [Semiring A]

open Matrix in
/-- `Bᴴ` is the adjoint of `B` for the standard Hermitian form. -/
lemma star_mulVec_dotProduct {m n : Type*} [Fintype m] [Fintype n] [StarRing A] (B : Matrix m n A)
    (x : n → A) (y : m → A) :
    star (B *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ Bᴴ *ᵥ y := by
  rw [star_mulVec, dotProduct_mulVec]
