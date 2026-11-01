import DiophantineConsistency.AdaptiveNamedValues47Model
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues47
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011

def literal (p : Fin 4 → ℤ) : Expr (Fin 47) := AdaptiveNamedValues47Context.literal p

theorem literal_eq (p : Fin 4 → ℤ) : literal p = AdaptiveNamedValues47Context.literal p := by rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_no_zero_iff :
    (∀ v : Fin 47 → V, ¬ InternalZero (positiveShift (literal CurrentWindowCarry2011.ports)) v) ↔
    (∀ v : Fin 42 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues42.literal CurrentWindowCarry2011.ports)) v) := by
  exact (AdaptiveNamedValues47Model.shifted_no_zero_iff (V:=V) CurrentWindowCarry2011.ports).trans
    (AdaptiveNamedValues49.current_no_zero_iff (V:=V))
end DiophantineConsistency.AdaptiveNamedValues47
