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
  have hparams := scaled_parameters_positive p v hb hv
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := expressionAt_quotients86 p v hb hv hz
  have hq : 0<1+v 0*(p 0:V) := lt_trans (by simp : (0:V)<1) hparams.1
  have hQ : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) :=
    mul_pos hq (mul_pos hq hq)
  obtain ⟨s,hs⟩ := quotient_forces_Y_divisible p v hparams.2.1 hQ t ht
  exact ⟨s,pos_of_mul_pos_right (by rw [←hs]; exact hv 7) (by simp),hs⟩

theorem expressionAt_main_oriented86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : MainOriented p v := by
  exact main_oriented_of_facts p v hb hv (expressionAt_quotients86 p v hb hv hz)
    (expressionAt_transport_positive86 p v hb hv hz) (expressionAt_Y_quotient86 p v hb hv hz)

end DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation
