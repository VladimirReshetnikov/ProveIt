import DiophantineConsistency.Sign32GenericRemoveInput
import DiophantineConsistency.Sign32CurrentSourceIff

/-! UNCOMPILED symbolic-port input-substitution definition only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32AbstractExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  Sign32GenericRemoveInput.removeInput (SharingSeed32Sextic.seed p)

end DiophantineConsistency.Sign32AbstractExpression
