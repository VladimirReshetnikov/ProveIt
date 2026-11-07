import DiophantineConsistency.Sign32CurrentSourceIff
import DiophantineConsistency.ModelJonesSyntax

/-! UNCOMPILED 32-coordinate expression: substitute fixed input 1 syntactically. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32DirectExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression : Expr (Fin 32) :=
  (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports).subst
    (Fin.cons (.constant 1) (fun i => .var i))

theorem eval_expression (w : Fin 32 → V) :
    expression.evalRing (fun i => ι (w i)) =
      (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports).evalRing
        (fun i => ι (Fin.cons (1 : V) w i)) := by
  rw [expression, ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Expr.evalRing, map_one]
  · simp [Expr.evalRing]

theorem zero_iff_current :
    (∃ w : Fin 32 → V, InternalZero expression w) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have hleft : (∃ w : Fin 32 → V, InternalZero expression w) ↔
      ∃ w : Fin 32 → V, InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, eval_expression]
  exact hleft.trans Sign32CurrentSourceIff.seed_exists_iff_source
end DiophantineConsistency.Sign32DirectExpression
#print axioms DiophantineConsistency.Sign32DirectExpression.eval_expression
#print axioms DiophantineConsistency.Sign32DirectExpression.zero_iff_current
