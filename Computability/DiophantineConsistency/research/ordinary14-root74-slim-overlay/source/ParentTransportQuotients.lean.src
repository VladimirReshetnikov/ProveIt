import ParentScaledNorms
import DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011

/-! Source-only transport of a 13-parent own zero through existing Fin13
fact interfaces. No target graph zero or Lean elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ParentTransportQuotientsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveQuotients2011
open ArithmeticAdaptiveFirstDivisibility2011 ArithmeticAdaptiveTransport2011
open ArithmeticAdaptiveTransportQuotient2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same positive parent zero supplies both scaled-root quotients,
positive Bt=b*t, and a positive q³ ordinate quotient. Ports are natural;
no upper bound on K or mask inequality is assumed. -/
theorem quotient_bundle (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P88FourSquare.graph (fun j => (p j : ℤ))).output v) :
    Quotients p v ∧ TransportQuotient p v ∧
      ∃ s : V, 0<s ∧ v 7=((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s := by
  have hp := scaled_parameters_positive p v hb hv
  have hn := ParentScaledNormsDraft.scaled_norms p v hz
  have hq := quotients_of_scaled_norms p v hp.2.1 hp.2.2.1 hn
  have hpos := quotients_force_transport p v hb hv hq
  obtain ⟨tau,d,htau,hd,hfirst,hnfirst,hmain,hnmain⟩ := hq
  have htrans := quotient_transport p v hp.2.1 hpos tau hfirst
  have hY := positive_Y_quotient_of_facts p v hp.2.1 (hv 7) hq
  exact ⟨hq,htrans,hY⟩

end DiophantineConsistency.ParentTransportQuotientsDraft

#print axioms DiophantineConsistency.ParentTransportQuotientsDraft.quotient_bundle
