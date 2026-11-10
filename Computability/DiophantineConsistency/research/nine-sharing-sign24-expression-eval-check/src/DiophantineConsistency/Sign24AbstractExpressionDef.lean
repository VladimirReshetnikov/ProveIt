import DiophantineConsistency.Sign32GenericRemoveInput
import DiophantineConsistency.SharingSeed24Octic

/-! SOURCE-ONLY UNCOMPILED symbolic-port input-substitution definition only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24AbstractExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  Sign32GenericRemoveInput.removeInput (SharingSeed24Octic.seed p)

end DiophantineConsistency.Sign24AbstractExpression
