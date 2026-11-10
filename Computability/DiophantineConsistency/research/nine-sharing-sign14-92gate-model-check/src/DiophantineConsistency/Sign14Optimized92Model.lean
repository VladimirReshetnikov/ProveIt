import DiophantineConsistency.Sign14Optimized92Expression

/-! SOURCE-ONLY: zero equivalence in every IΣ₁ model. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized92Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff (p : Fin 4 → ℤ) (w : Fin 14 → V) :
    InternalZero (Sign14Optimized92Expression.expression p) w ↔
      InternalZero (Sign32GenericRemoveInput.removeInput (Sign14Optimized93.seed p)) w := by
  simp only [internalZero_iff, Sign14Optimized92Expression.eval_expression]

theorem zero_exists_iff (p : Fin 4 → ℤ) :
    (∃ w : Fin 14 → V, InternalZero (Sign14Optimized92Expression.expression p) w) ↔
      ∃ w : Fin 14 → V, InternalZero (Sign32GenericRemoveInput.removeInput (Sign14Optimized93.seed p)) w := by
  exact exists_congr (zero_iff p)
end DiophantineConsistency.Sign14Optimized92Model
#print axioms DiophantineConsistency.Sign14Optimized92Model.zero_iff
#print axioms DiophantineConsistency.Sign14Optimized92Model.zero_exists_iff
