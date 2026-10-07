/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Map

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem baseChange_coordinate_eq
    {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ V) (c : Basis κ ℚ W) (P : V →ₗ[ℚ] W) (r : κ → ι)
    (hP : ∀ x i, c.repr (P x) i = b.repr x (r i))
    (x : ℝ ⊗[ℚ] V) (i : κ) :
    (c.baseChange ℝ).repr (P.baseChange ℝ x) i = (b.baseChange ℝ).repr x (r i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul t x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, hP]

theorem baseChange_coordinate_projector_repr
    {V W ι : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ V) (P : V →ₗ[ℚ] W) (S : W →ₗ[ℚ] V)
    (p : ι → Prop) [DecidablePred p]
    (hproj : ∀ x i, b.repr (S (P x)) i = if p i then b.repr x i else 0)
    (x : ℝ ⊗[ℚ] V) (i : ι) :
    (b.baseChange ℝ).repr (S.baseChange ℝ (P.baseChange ℝ x)) i =
      if p i then (b.baseChange ℝ).repr x i else 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply] at *
    rw [hx, hy]
    split_ifs <;> simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, hproj]
    split_ifs <;> simp

end Erdos3

end

end OAI
