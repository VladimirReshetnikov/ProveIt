import DiophantineConsistency.AdaptiveDirectOrdinate86Quotients
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! Positive transport from an actual direct-ordinate zero and positive inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveTransport2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Quotients
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expressionAt_transport_positive86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : TransportPositive p v :=
  quotients_force_transport p v hb hv (expressionAt_quotients86 p v hb hv hz)
end DiophantineConsistency.AdaptiveDirectOrdinate86Transport
