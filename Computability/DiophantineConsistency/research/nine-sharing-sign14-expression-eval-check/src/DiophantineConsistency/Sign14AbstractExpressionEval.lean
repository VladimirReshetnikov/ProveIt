import DiophantineConsistency.Sign14AbstractExpressionDef

/-! SOURCE-ONLY UNCOMPILED symbolic-port evaluation theorem in its own stage. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AbstractExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_expression (p : Fin 4 → ℤ) (w : Fin 14 → V) :
    (expression p).evalRing (fun i => ι (w i)) =
      (SharingSeed14Degree124.seed p).evalRing (fun i => ι (Fin.cons (1 : V) w i)) := by
  change (Sign32GenericRemoveInput.removeInput (SharingSeed14Degree124.seed p)).evalRing (fun i => ι (w i)) = _
  rw [Sign32GenericRemoveInput.eval_removeInput]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [map_one]
  · simp
end DiophantineConsistency.Sign14AbstractExpression
#print axioms DiophantineConsistency.Sign14AbstractExpression.eval_expression
