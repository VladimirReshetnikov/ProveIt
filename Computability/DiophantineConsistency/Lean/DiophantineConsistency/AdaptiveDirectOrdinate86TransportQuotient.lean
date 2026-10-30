import DiophantineConsistency.AdaptiveDirectOrdinate86Transport
import DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011

/-! Positive transport quotient from an actual direct-ordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86TransportQuotient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransportQuotient2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Quotients AdaptiveDirectOrdinate86Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expressionAt_transport_quotient86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : TransportQuotient p v := by
  have hp := scaled_parameters_positive p v hb hv
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := expressionAt_quotients86 p v hb hv hz
  exact quotient_transport p v hp.2.1 (expressionAt_transport_positive86 p v hb hv hz) t ht
end DiophantineConsistency.AdaptiveDirectOrdinate86TransportQuotient
