import DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveTransportQuotient2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (p : Fin 4 → ℕ) (v : Fin 13 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : TransportQuotient p v :=
  expressionAt_transport_quotient p v hb hv hz
#print axioms quotient_transport
#print axioms expressionAt_transport_quotient
end DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011Checks
