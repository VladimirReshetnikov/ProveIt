/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realifyFunctional_lie_eq_zero (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) (x y : ℝ ⊗[ℚ] L) :
    realifyFunctional η ⁅x, y⁆ = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, realifyFunctional_tmul,
        hη, Rat.cast_zero, mul_zero]
    | add y z hy hz => simp only [LieRing.lie_add, map_add, hy, hz, add_zero]
  | add x z hx hz => simp only [LieRing.add_lie, map_add, hx, hz, add_zero]

attribute [local instance] LieRing.ofAssociativeRing

noncomputable def realifyFunctionalLie (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) : (ℝ ⊗[ℚ] L) →ₗ⁅ℚ⁆ ℝ where
  toLinearMap := (realifyFunctional η).restrictScalars ℚ
  map_lie' {x y} := by
    change realifyFunctional η ⁅x, y⁆ = ⁅realifyFunctional η x, realifyFunctional η y⁆
    rw [realifyFunctional_lie_eq_zero η hη]
    simp only [Ring.lie_def, mul_comm, sub_self]

theorem realifyFunctional_lieBCH (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s)
    (x y : ℝ ⊗[ℚ] L) :
    realifyFunctional η (lieBCH s x y) = realifyFunctional η x + realifyFunctional η y := by
  change realifyFunctionalLie η hη (lieBCH s x y) = _
  rw [map_lieBCH, lieBCH_eq_add_of_lie_eq_zero_pos hs
    (by simp only [Ring.lie_def, mul_comm, sub_self])]
  rfl

end Erdos3

end

end OAI
