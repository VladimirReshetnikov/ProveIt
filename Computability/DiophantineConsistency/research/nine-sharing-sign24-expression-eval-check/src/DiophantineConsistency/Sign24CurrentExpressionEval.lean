import DiophantineConsistency.Sign24CurrentExpressionDef

/-! SOURCE-ONLY UNCOMPILED current-port evaluation specialization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24CurrentExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem eval_expression (w : Fin 24 → V) :
    expression.evalRing (fun i => ι (w i)) =
      (SharingSeed24Octic.seed CurrentWindowCarry2011.ports).evalRing
        (fun i => ι (Fin.cons (1 : V) w i)) := by
  exact Sign24AbstractExpression.eval_expression CurrentWindowCarry2011.ports w
end DiophantineConsistency.Sign24CurrentExpression
#print axioms DiophantineConsistency.Sign24CurrentExpression.eval_expression
