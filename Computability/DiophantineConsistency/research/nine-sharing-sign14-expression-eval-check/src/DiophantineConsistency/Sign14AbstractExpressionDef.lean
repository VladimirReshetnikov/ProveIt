import DiophantineConsistency.Sign32GenericRemoveInput
import DiophantineConsistency.SharingSeed14Degree124

/-! SOURCE-ONLY UNCOMPILED symbolic-port input-substitution definition only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AbstractExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def expression (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  Sign32GenericRemoveInput.removeInput (SharingSeed14Degree124.seed p)

end DiophantineConsistency.Sign14AbstractExpression
