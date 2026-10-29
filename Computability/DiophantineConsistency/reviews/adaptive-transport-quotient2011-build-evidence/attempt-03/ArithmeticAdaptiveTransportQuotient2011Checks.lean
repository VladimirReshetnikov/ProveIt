import DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveTransportQuotient2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (p : Fin 4 → ℕ) (v : Fin 13 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : TransportQuotient p v :=
  expressionAt_transport_quotient p v hb hv hz
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    TransportQuotient currentPorts (fun j => v j+1) := current_natural_transport_quotient v hz
#print axioms current_transport_quotient
#print axioms current_natural_transport_quotient
#print axioms quotient_transport
#print axioms expressionAt_transport_quotient
end DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011Checks
