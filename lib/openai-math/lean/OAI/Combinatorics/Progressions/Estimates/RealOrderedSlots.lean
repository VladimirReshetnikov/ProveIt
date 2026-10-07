import OAI.Combinatorics.Progressions.Geometry.ControlledIntegralCoordinates

namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realOrderedSlots (B : ℝ) (a : NilpotentLieBCHGroup L s hnil) :
    TriangularSlots d where
  center x j := -e.repr (a * realOrderedBasisPrefixProduct e hnil j.val
    (fun k => B * x k)).coord j / B
  lower j x y h := by
    have hp : realOrderedBasisPrefixProduct e hnil j.val (fun k => B * x k) =
        realOrderedBasisPrefixProduct e hnil j.val (fun k => B * y k) := by
      apply realOrderedBasisPrefixProduct_congr
      intro k hk
      rw [h k hk]
    rw [hp]

namespace IsRealCentralLieBasis

variable [IsScalarTower ℚ ℝ L] {e} (he : IsRealCentralLieBasis e)
include he

theorem realOrderedSlots_residual (B : ℝ) (hB : B ≠ 0)
    (a : NilpotentLieBCHGroup L s hnil) (b : Fin d → ℤ) :
    (realOrderedSlots e hnil B a).residual b = fun j =>
      e.repr (a * realOrderedBasisProduct e hnil (fun k => B * (b k : ℝ))).coord j / B := by
  funext j
  dsimp only [TriangularSlots.residual, realOrderedSlots]
  rw [he.mul_realOrderedBasisProduct_coordinate hnil]
  field_simp; ring

theorem smul_realOrderedSlots_residual (B : ℝ) (hB : B ≠ 0)
    (a : NilpotentLieBCHGroup L s hnil) (b : Fin d → ℤ) :
    B • (realOrderedSlots e hnil B a).residual b =
      e.equivFun (a * realOrderedBasisProduct e hnil (fun k => B * (b k : ℝ))).coord := by
  rw [he.realOrderedSlots_residual hnil B hB]
  funext j
  change B * (_ / B) = _
  exact mul_div_cancel₀ _ hB

end IsRealCentralLieBasis
end Erdos3

end

end OAI
