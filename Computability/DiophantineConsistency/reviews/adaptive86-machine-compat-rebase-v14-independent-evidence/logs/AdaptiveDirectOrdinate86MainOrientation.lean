import DiophantineConsistency.AdaptiveDirectOrdinate86CompatHelpers
import DiophantineConsistency.AdaptiveDirectOrdinate86TransportQuotient
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

/-! Positive main root from the actual direct-ordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Quotients AdaptiveDirectOrdinate86Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem expressionAt_Y_quotient86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) :
    ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s := by
  exact positive_Y_quotient_of_facts p v (scaled_parameters_positive p v hb hv).2.1
    (hv 7) (expressionAt_quotients86 p v hb hv hz)

theorem expressionAt_main_oriented86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : MainOriented p v := by
  exact main_oriented_of_facts p v hb hv (expressionAt_quotients86 p v hb hv hz)
    (expressionAt_transport_positive86 p v hb hv hz) (expressionAt_Y_quotient86 p v hb hv hz)

end DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation
