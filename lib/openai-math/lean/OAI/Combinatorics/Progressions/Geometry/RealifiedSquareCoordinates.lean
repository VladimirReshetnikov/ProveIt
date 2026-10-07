/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Prod
import OAI.Combinatorics.Progressions.Linear.SquareBasisGeometry

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareEquiv :
    (ℝ ⊗[ℚ] F.squareLieSubalgebra) ≃ₗ[ℚ] F.realification.squareLieSubalgebra :=
  let e := ((F.squareCoordinates.baseChange ℚ ℝ _ _).trans
    (TensorProduct.prodRight ℚ ℝ ℝ L (F.layer 2))).trans
      ((LinearEquiv.refl ℝ (ℝ ⊗[ℚ] L)).prodCongr (realificationSubmoduleEquiv (F.layer 2)))
  (e.restrictScalars ℚ).trans F.realification.squareCoordinates.symm

theorem realifiedSquareEquiv_tmul (r : ℝ) (x : F.squareLieSubalgebra) :
    (F.realifiedSquareEquiv (r ⊗ₜ[ℚ] x)).val =
      (r ⊗ₜ[ℚ] x.val.1, r ⊗ₜ[ℚ] x.val.2) := by
  apply Prod.ext
  · change r ⊗ₜ[ℚ] x.val.2 + r ⊗ₜ[ℚ] (x.val.1 - x.val.2) = r ⊗ₜ[ℚ] x.val.1
    rw [← TensorProduct.tmul_add]
    congr 1
    abel
  · rfl

theorem realifiedSquareEquiv_fst (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    F.realification.squareFst (F.realifiedSquareEquiv x) = realificationLieHom F.squareFst x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => exact congrArg Prod.fst (F.realifiedSquareEquiv_tmul r x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realifiedSquareEquiv_snd (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    F.realification.squareSnd (F.realifiedSquareEquiv x) = realificationLieHom F.squareSnd x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => exact congrArg Prod.snd (F.realifiedSquareEquiv_tmul r x)
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realifiedSquareLieEquiv :
    (ℝ ⊗[ℚ] F.squareLieSubalgebra) ≃ₗ⁅ℚ⁆ F.realification.squareLieSubalgebra where
  toFun := F.realifiedSquareEquiv
  invFun := F.realifiedSquareEquiv.symm
  left_inv := F.realifiedSquareEquiv.left_inv
  right_inv := F.realifiedSquareEquiv.right_inv
  map_add' := F.realifiedSquareEquiv.map_add
  map_smul' := F.realifiedSquareEquiv.map_smul
  map_lie' := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · change F.realification.squareFst (F.realifiedSquareEquiv ⁅x, y⁆) =
        F.realification.squareFst ⁅F.realifiedSquareEquiv x, F.realifiedSquareEquiv y⁆
      simp only [realifiedSquareEquiv_fst, LieHom.map_lie]
    · change F.realification.squareSnd (F.realifiedSquareEquiv ⁅x, y⁆) =
        F.realification.squareSnd ⁅F.realifiedSquareEquiv x, F.realifiedSquareEquiv y⁆
      simp only [realifiedSquareEquiv_snd, LieHom.map_lie]

end Erdos3.NilpotentLieFiltration

end

end OAI
