import DiophantineConsistency.Sign32GenericRemoveInput
import DiophantineConsistency.Sign32CurrentSourceIff

/-! UNCOMPILED concrete expression and evaluation via the generic theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32DirectExpressionSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression : Expr (Fin 32) :=
  Sign32GenericRemoveInput.removeInput (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports)

theorem eval_expression (w : Fin 32 → V) :
    expression.evalRing (fun i => ι (w i)) =
      (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports).evalRing
        (fun i => ι (Fin.cons (1 : V) w i)) := by
  change (Sign32GenericRemoveInput.removeInput (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports)).evalRing (fun i => ι (w i)) = _
  rw [Sign32GenericRemoveInput.eval_removeInput]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [map_one]
  · simp
end DiophantineConsistency.Sign32DirectExpressionSplit
#print axioms DiophantineConsistency.Sign32DirectExpressionSplit.eval_expression
