import DiophantineConsistency.Sign14Positive74ExpressionBridge

/-! SOURCE-ONLY: model-zero transport for positive-coordinate expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff (p : Fin 4 → ℤ) (w : Fin 14 → V) :
    InternalZero (positiveShift (Sign14Positive74.expression p)) w ↔
      InternalZero (Sign14Optimized86Expression.expression p) w := by
  rw [internalZero_positiveShift, internalZero_iff, internalZero_iff]
  simpa only [map_add, map_one] using
    (iff_of_eq (congrArg (fun z : DiffRing V => z = 0)
      (Sign14Positive74ExpressionBridge.eval_shift p (fun i => ι (w i)))))

theorem zero_exists_iff (p : Fin 4 → ℤ) :
    (∃ w : Fin 14 → V, InternalZero (positiveShift (Sign14Positive74.expression p)) w) ↔
      ∃ w : Fin 14 → V, InternalZero (Sign14Optimized86Expression.expression p) w := by
  exact exists_congr (zero_iff p)
end DiophantineConsistency.Sign14Positive74Model
#print axioms DiophantineConsistency.Sign14Positive74Model.zero_iff
#print axioms DiophantineConsistency.Sign14Positive74Model.zero_exists_iff
