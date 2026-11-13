import DiophantineConsistency.Sign32GenericRemoveInput
import DiophantineConsistency.SharingSeed25Octic

/-! SOURCE-ONLY UNCOMPILED symbolic-port input-substitution definition only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25AbstractExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  Sign32GenericRemoveInput.removeInput (SharingSeed25Octic.seed p)

end DiophantineConsistency.Sign25AbstractExpression
