import DiophantineConsistency.Sign32GenericRemoveInput
import DiophantineConsistency.SharingSeed26Sextic

/-! SOURCE-ONLY UNCOMPILED symbolic-port input-substitution definition only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26AbstractExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  Sign32GenericRemoveInput.removeInput (SharingSeed26Sextic.seed p)

end DiophantineConsistency.Sign26AbstractExpression
