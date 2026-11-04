import DiophantineConsistency.Compact44.ReducedNormNext
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ReducedNormState
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.ArithmeticGcdNormalization
open ReducedNormBounds ReducedNormNext
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem smaller_reduced_state {r v a b : V} (hr : 0<r) (hv : 1<v) (hb : 0<b)
    (hu : Bez a b 1) (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) :
    ∃ s k t : V, r=(b*b)*s ∧ 0<k ∧ k<v ∧ Bez t b 1 ∧
      (r+1)*(k*b)*(k*b)=r*(t*t)+b*b ∧
      (let vp : DiffRing V := (2*ι r+1)*ι v-2*ι b*ι s*ι a
       (ι k=vp ∨ ι k= -vp)) ∧
      (let ap : DiffRing V := (2*ι r+1)*ι a-2*(ι r+1)*ι v*ι b
       (ι t=ap ∨ ι t= -ap)) := by
  obtain ⟨s,k,hs,hkpos,hklt,hksign⟩ := model_smaller_first hr hv hb hu hn
  obtain ⟨u,t,hu',htsign,htbez⟩ := model_signed_numerator hu hn
  have heq : s=u := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos hb hb))
    exact hs.symm.trans hu'
  subst u
  let R := ι r
  let B := ι b
  let vp : DiffRing V := (2*R+1)*ι v-2*B*ι s*ι a
  let ap : DiffRing V := (2*R+1)*ι a-2*(R+1)*ι v*B
  change ι k=vp ∨ ι k= -vp at hksign
  change ι t=ap ∨ ι t= -ap at htsign
  have hksq : ι k*ι k=vp*vp := by
    rcases hksign with h | h
    · rw [h]
    · rw [h]; ring
  have htsq : ι t*ι t=ap*ap := by
    rcases htsign with h | h
    · rw [h]
    · rw [h]; ring
  have hs' : R=B*B*ι s := by
    simpa only [R,B,map_mul] using congrArg (fun x : V => ι x) hs
  have hn' : (R+1)*(ι v*B)*(ι v*B)=R*(ι a*ι a)+B*B := by
    simpa only [R,B,map_add,map_mul,map_one] using congrArg (fun x : V => ι x) hn
  have hn0 : (R+1)*ι v*ι v*B*B-R*ι a*ι a-B*B=0 := by
    calc
      _=(R+1)*(ι v*B)*(ι v*B)-(R*(ι a*ι a)+B*B) := by ring
      _=0 := by rw [hn']; ring
  have hnnew : (R+1)*vp*vp*B*B-R*ap*ap-B*B=0 := by
    rw [ring_transform_norm R (ι v) (ι a) B (ι s) hs',hn0]
  have hneweq : (R+1)*vp*vp*B*B=R*ap*ap+B*B := by linarith
  refine ⟨s,k,t,hs,hkpos,hklt,htbez,?_,?_,?_⟩
  · apply ι_injective
    simp only [map_add,map_mul,map_one]
    change (R+1)*(ι k*B)*(ι k*B)=R*(ι t*ι t)+B*B
    calc
      _=(R+1)*(ι k*ι k)*B*B := by ring
      _=(R+1)*vp*vp*B*B := by rw [hksq]; ring
      _=R*ap*ap+B*B := hneweq
      _=R*(ι t*ι t)+B*B := by rw [htsq]; ring
  · exact hksign
  · exact htsign
end ReducedNormState
#print axioms ReducedNormState.smaller_reduced_state
