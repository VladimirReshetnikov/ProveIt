import DiophantineConsistency.ArithmeticAdaptiveTransport2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransport2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveTransport2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (p : Fin 4 → ℕ) (v : Fin 13 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : TransportPositive p v :=
  expressionAt_transport_positive p v hb hv hz
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    TransportPositive currentPorts (fun j => v j+1) := current_natural_transport_positive v hz
#print axioms current_transport_positive
#print axioms current_natural_transport_positive
#print axioms magnitude_equivalent
#print axioms first_root_bound
#print axioms quotients_force_transport
#print axioms expressionAt_transport_positive
end DiophantineConsistency.ArithmeticAdaptiveTransport2011Checks
