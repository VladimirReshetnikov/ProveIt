import NormsToBounds
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! Source-only factor-level extraction. The ring residual equations and
coefficient identities are explicit premises, not extracted from a graph
zero here. Imports include uncompiled drafts. No Lean elaboration occurred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AuxRingNormExtractionDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticAdaptiveQuotients2011 AuxNormsToBoundsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A signed difference-ring square scaled by a positive natural square has
an unscaled natural square root; no sign/orientation for Z is assumed. -/
theorem root_of_scaled_ring_square (U n : V) (Z : DiffRing V) (hU : 0<U)
    (h : Z*Z=(ι U*ι U)*ι n) : ∃ d : V, d*d=n := by
  rcases nonneg_or_nonpos Z with ⟨z,hz⟩ | ⟨z,hz⟩
  · have hsq : z*z=U*U*n := by
      apply ι_injective
      rw [hz] at h
      simpa only [map_mul] using h
    obtain ⟨d,_,hd⟩ := scaled_quotient U z n hU hsq
    exact ⟨d,hd⟩
  · have hsq : z*z=U*U*n := by
      apply ι_injective
      rw [hz] at h
      simpa only [neg_mul_neg,map_mul] using h
    obtain ⟨d,_,hd⟩ := scaled_quotient U z n hU hsq
    exact ⟨d,hd⟩

/-- The direct first residual yields the natural first Pell norm. -/
theorem first_norm_of_ring_residual (X Y eta zeta tau : V)
    (h : ι tau*ι tau-
      ι (1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta)))=0) :
    tau*tau=1+(X*Y*Y)*(X*Y*Y+1)*(eta+zeta)*(eta+zeta) := by
  have hs : tau*tau=1+((X*Y)*(Y*(eta+zeta)))*
      (((X*Y)*(Y*(eta+zeta)))+(eta+zeta)) := by
    apply ι_injective
    simpa only [map_mul] using (sub_eq_zero.mp h)
  calc
    tau*tau=1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta)) := hs
    _=1+(X*Y*Y)*(X*Y*Y+1)*(eta+zeta)*(eta+zeta) := by ring

/-- A strong residual gives the natural norm without introducing natural
subtraction. c and Delta remain arbitrary natural parameters. -/
theorem strong_norm_of_ring_residual (c i Delta f : V)
    (h : (ι i*ι c*ι c)*(ι i*ι c*ι c)-ι Delta*(ι f*ι f-1)=0) :
    (i*c*c)*(i*c*c)+Delta=Delta*(f*f) := by
  have hs : (ι i*ι c*ι c)*(ι i*ι c*ι c)=ι Delta*(ι f*ι f-1) := sub_eq_zero.mp h
  have he : (ι i*ι c*ι c)*(ι i*ι c*ι c)+ι Delta=ι Delta*(ι f*ι f) := by
    rw [hs]
    ring
  apply ι_injective
  simpa only [map_add,map_mul] using he

/-- Proposed fact-level composition from explicit direct field residuals to
both strict auxiliary bounds. A graph client must supply these premises. -/
theorem bounds_of_direct_field_residuals
    (X Y eta zeta tau Delta c i f U : V) (Z z Q t : DiffRing V)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta) (hi : 0<i) (hU : 0<U)
    (hcdef : c=eta+Y*(eta+zeta))
    (hDeltaDef : Delta=3+4*(X*Y+Y)+(X*Y+Y)*(X*Y+Y))
    (hfirst : ι tau*ι tau-
      ι (1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta)))=0)
    (hmain : Z*Z-(ι U*ι U)*ι (1+Delta*c*c)=0)
    (hstrong : (ι i*ι c*ι c)*(ι i*ι c*ι c)-ι Delta*(ι f*ι f-1)=0)
    (hQ : Q=(ι i*ι c*ι c)*(ι i*ι c*ι c))
    (hz : z+ι c=(ι f*ι f)*t) : 1<Q ∧ 1<z*z := by
  have hfirstN := first_norm_of_ring_residual X Y eta zeta tau hfirst
  have hstrongN := strong_norm_of_ring_residual c i Delta f hstrong
  obtain ⟨d,hd⟩ := root_of_scaled_ring_square U (1+Delta*c*c) Z hU (sub_eq_zero.mp hmain)
  have hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1 := by rw [hDeltaDef]; ring
  exact aux_bounds_of_natural_norms X Y eta zeta tau d Delta c i f z Q t
    hX hY heta hzeta hi hcdef hDelta hfirstN hd hstrongN hQ hz

end DiophantineConsistency.AuxRingNormExtractionDraft

#print axioms DiophantineConsistency.AuxRingNormExtractionDraft.root_of_scaled_ring_square
#print axioms DiophantineConsistency.AuxRingNormExtractionDraft.first_norm_of_ring_residual
#print axioms DiophantineConsistency.AuxRingNormExtractionDraft.strong_norm_of_ring_residual
#print axioms DiophantineConsistency.AuxRingNormExtractionDraft.bounds_of_direct_field_residuals
