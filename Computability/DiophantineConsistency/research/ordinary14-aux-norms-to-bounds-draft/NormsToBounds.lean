import MainSquareGap
import AuxRootBounds
import AuxGeometry

/-! Source-only composition of uncompiled fact-level proposals. Every natural
norm, signed expression and strong coefficient is an explicit premise; no
literal graph or endpoint is imported. No Lean elaboration has occurred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AuxNormsToBoundsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ModelMainSquareGapDraft AuxRootBoundsModelDraft AuxGeometryModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed model-level composition: natural first/main/strong norms and
explicit signed V/strong coefficient identities give the two strict bounds
used by the conditional auxiliary-root witness lemma. -/
theorem aux_bounds_of_natural_norms
    (X Y eta zeta tau d Delta c i f : V) (z Q t : DiffRing V)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta) (hi : 0<i)
    (hcdef : c=eta+Y*(eta+zeta))
    (hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1)
    (hfirst : tau*tau=1+(X*Y*Y)*(X*Y*Y+1)*(eta+zeta)*(eta+zeta))
    (hmain : d*d=1+Delta*c*c)
    (hstrong : (i*c*c)*(i*c*c)+Delta=Delta*(f*f))
    (hQ : Q=(ι i*ι c*ι c)*(ι i*ι c*ι c))
    (hz : z+ι c=(ι f*ι f)*t) : 1<Q ∧ 1<z*z := by
  have hmain' : d*d=1+Delta*(eta+Y*(eta+zeta))*(eta+Y*(eta+zeta)) := by
    simpa only [hcdef] using hmain
  have hkne : eta+zeta≠2 :=
    two_ordinate_impossible X Y eta zeta Delta d hX hY heta hzeta hDelta hmain'
  have hkge : (2:V)≤eta+zeta := by
    have h := add_le_add (pos_iff_one_le.mp heta) (pos_iff_one_le.mp hzeta)
    simpa only [show (1:V)+1=2 by ring] using h
  have hkgt : 2<eta+zeta := lt_of_le_of_ne hkge (Ne.symm hkne)
  have hm : 0<X*Y*Y := mul_pos (mul_pos hX hY) hY
  have hkLarge0 := first_ordinate_large (X*Y*Y) tau (eta+zeta) hm hkgt hfirst
  have hkLarge : 8*X*Y*Y+4≤eta+zeta := by
    simpa only [show 8*(X*Y*Y)=8*X*Y*Y by ring] using hkLarge0
  have hgeo := geometry_of_large_k X Y eta (eta+zeta) Delta hY heta hkLarge hDelta
  dsimp only at hgeo
  rcases hgeo with ⟨_,hc,hdpos,hdsmall⟩
  have hc' : 1<c := by rw [hcdef]; exact hc
  have hdsmall' : Delta<c*c*c := by rw [hcdef]; exact hdsmall
  have hcR : (1 : DiffRing V)<ι c := by
    have h := (ι_lt_ι (a := (1:V)) (b := c)).mpr hc'
    simpa only [map_one] using h
  have hiR : (1 : DiffRing V)≤ι i := by
    have h := (ι_le_ι (a := (1:V)) (b := i)).mpr (pos_iff_one_le.mp hi)
    simpa only [map_one] using h
  have hdposR : (0 : DiffRing V)<ι Delta := by
    have h := (ι_lt_ι (a := (0:V)) (b := Delta)).mpr hdpos
    simpa only [map_zero] using h
  have hdsmallR : ι Delta<ι c*ι c*ι c := by
    have h := (ι_lt_ι (a := Delta) (b := c*c*c)).mpr hdsmall'
    simpa only [map_mul] using h
  have hstrongR : (ι i*ι c*ι c)*(ι i*ι c*ι c)+ι Delta=ι Delta*(ι f*ι f) := by
    have h := congrArg (ι : V →+* DiffRing V) hstrong
    simpa only [map_add,map_mul] using h
  have hcposR : (0 : DiffRing V)<ι c := lt_trans (by norm_num) hcR
  have hfR : ι c+1<ι f*ι f :=
    strong_f_square_large (ι c) (ι i) (ι Delta) (ι f) hcposR hiR hdposR hdsmallR hstrongR
  have hQR : 1<Q := strong_Q_gt_one (ι c) (ι i) Q hcR hiR hQ
  have hzR : 1<z*z := signed_square_gt_one (ι c) (ι f) t z hcR hfR hz
  exact ⟨hQR,hzR⟩

end DiophantineConsistency.AuxNormsToBoundsDraft

#print axioms DiophantineConsistency.AuxNormsToBoundsDraft.aux_bounds_of_natural_norms
