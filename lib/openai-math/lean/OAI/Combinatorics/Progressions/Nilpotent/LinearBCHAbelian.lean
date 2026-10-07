/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Lie.BaseChange
import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem linearMap_lieBCH_eq_add {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    f (lieBCH s a b) = f a + f b := by
  let : LieRing V := {
    toAddCommGroup := inferInstance
    bracket := fun _ _ => 0
    add_lie := fun _ _ _ => (add_zero 0).symm
    lie_add := fun _ _ _ => (add_zero 0).symm
    lie_self := fun _ => rfl
    leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  let : LieAlgebra ℚ V := {
    toModule := inferInstance
    lie_smul := fun t _ _ => (smul_zero t).symm }
  let : IsLieAbelian V := ⟨fun _ _ => rfl⟩
  let φ : L →ₗ⁅ℚ⁆ V := { f with map_lie' := fun {x y} => hf x y }
  exact (map_lieBCH φ s a b).trans (lieBCH_eq_add_of_isLieAbelian hs (f a) (f b))

theorem linearMap_baseChange_lie_eq_zero {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) (a b : ℝ ⊗[ℚ] L) :
    f.baseChange ℝ ⁅a, b⁆ = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul a x =>
    induction b using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.baseChange_tmul, hf,
        TensorProduct.tmul_zero]
    | add b c hb hc => rw [lie_add, map_add, hb, hc, add_zero]
  | add a b ha hb => rw [add_lie, map_add, ha, hb, add_zero]

theorem linearMap_baseChange_lieBCH_eq_add {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s) (a b : ℝ ⊗[ℚ] L) :
    f.baseChange ℝ (lieBCH s a b) = f.baseChange ℝ a + f.baseChange ℝ b :=
  linearMap_lieBCH_eq_add ((f.baseChange ℝ).restrictScalars ℚ)
    (linearMap_baseChange_lie_eq_zero f hf) hs a b

end Erdos3

end

end OAI
