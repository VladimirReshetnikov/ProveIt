/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieHom_eq_self (φ : L →ₗ⁅ℚ⁆ L) (hφ : ∀ x, φ x = x)
    (x : ℝ ⊗[ℚ] L) : realificationLieHom φ x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rw [realificationLieHom_tmul, hφ]
  | add x y hx hy => rw [map_add, hx, hy]

theorem realificationLieHom_comp_apply (φ ψ θ : L →ₗ⁅ℚ⁆ L)
    (h : ∀ x, θ x = φ (ψ x)) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom θ x = realificationLieHom φ (realificationLieHom ψ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realificationLieHom_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realificationLieHom_eq_self_on (φ : L →ₗ⁅ℚ⁆ L) (U : Submodule ℚ L)
    (hφ : ∀ x ∈ U, φ x = x) (x : ℝ ⊗[ℚ] L) (hx : x ∈ U.baseChange ℝ) :
    realificationLieHom φ x = x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    simp only [LinearMap.baseChange_tmul, realificationLieHom_tmul]
    change r ⊗ₜ[ℚ] φ y.val = r ⊗ₜ[ℚ] y.val
    rw [hφ y.val y.property]
  | add y z hy hz => simp only [map_add, hy, hz]

end Erdos3

end

end OAI
