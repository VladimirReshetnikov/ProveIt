import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

noncomputable def scaledLinearResidual (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ) :
    V →ₗ[ℝ] V := q • LinearMap.id - T.comp E

theorem scaledLinearResidual_apply (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ) (x : V) :
    scaledLinearResidual E T q x = q • x - T (E x) := rfl

theorem scaledLinearResidual_evaluation (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ)
    (hT : ∀ x, E (T (E x)) = q • E x) (x : V) :
    E (scaledLinearResidual E T q x) = 0 := by
  rw [scaledLinearResidual_apply, map_sub, map_smul, hT, sub_self]

theorem scaledLinearResidual_on_kernel (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ)
    (x : V) (hx : E x = 0) : scaledLinearResidual E T q x = q • x := by
  rw [scaledLinearResidual_apply, hx, map_zero, sub_zero]

theorem scaledLinearResidual_factor_iff (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V)
    {q : ℝ} (hq : q ≠ 0) (hT : ∀ x, E (T (E x)) = q • E x) (L : V →ₗ[ℝ] ℝ) :
    L.comp (scaledLinearResidual E T q) = 0 ↔ ∃ M : W →ₗ[ℝ] ℝ, L = M.comp E := by
  constructor
  · intro h
    refine ⟨q⁻¹ • L.comp T, ?_⟩
    ext x
    have hx := DFunLike.congr_fun h x
    simp only [LinearMap.comp_apply, scaledLinearResidual_apply, map_sub, map_smul,
      smul_eq_mul, LinearMap.zero_apply, sub_eq_zero] at hx
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← hx, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  · rintro ⟨M, rfl⟩
    ext x
    simp only [LinearMap.comp_apply, scaledLinearResidual_evaluation E T q hT,
      map_zero, LinearMap.zero_apply]

end Erdos3

end

end OAI
