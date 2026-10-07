/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed
import OAI.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_neg {V : Type*} [AddCommGroup V] [Module ℚ V]
    (eta : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (-eta) x = -realifyFunctional eta x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realifyFunctional_tmul, LinearMap.neg_apply, Rat.cast_neg, mul_neg]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem conjugate_vertical (T : D.Niltest w) (eta : L →ₗ[ℚ] ℚ)
    (hvert : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = CircleFourier.character
        ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x)
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s) (x : D.Space) :
    T.conjugate.observable (z • x) = CircleFourier.character
      ((realifyFunctional (-eta) z.coord : ℝ) : CircleFourier.Circle) * T.conjugate.observable x := by
  change star (T.observable (z • x)) = _ * star (T.observable x)
  rw [hvert z hz x, star_mul, realifyFunctional_neg, AddCircle.coe_neg, CircleFourier.character_neg]
  exact mul_comm _ _

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
