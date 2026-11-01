import DiophantineConsistency.IPRANativeFormula

/-! The native NNF reading commutes with capture-avoiding rewriting. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeFormulaRew
open LO LO.FirstOrder IPRANativeFormula
open scoped LO.FirstOrder
variable {L : Language} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}

theorem native_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    ω ▹ native φ = native (ω ▹ φ) := by
  induction φ using Semiformula.rec' generalizing n₂ <;>
    simp [native, Semiformulaᵢ.rew_rel, *, Function.comp_def]
end DiophantineConsistency.IPRANativeFormulaRew
