import DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveRadix2011 ArithmeticAdaptiveTransportRestoration2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Radix (fun j => v j+1) ∧ RestoredTransport (fun j => v j+1) :=
  current_natural_transport_restoration v hz
#print axioms current_transport_restoration
#print axioms current_natural_transport_restoration
end DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011Checks
