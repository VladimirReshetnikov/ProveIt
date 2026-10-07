import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem independent_columns_of_nonzero_row_minor {K ι : Type*} [Field K] {k : ℕ}
    (Q : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (Q.submatrix p id).det ≠ 0) :
    LinearIndependent K Q.col := by
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  apply Matrix.mulVec_injective_of_isUnit
    ((Q.submatrix p id).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hp))
  funext i
  exact congrFun hxy (p i)

theorem independent_columns_of_identity_minor {K ι : Type*} [Field K] {k : ℕ}
    (Q : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : Q.submatrix p id = 1) :
    LinearIndependent K Q.col := by
  apply independent_columns_of_nonzero_row_minor Q p
  rw [hp, Matrix.det_one]
  exact one_ne_zero

end Erdos3

end

end OAI
