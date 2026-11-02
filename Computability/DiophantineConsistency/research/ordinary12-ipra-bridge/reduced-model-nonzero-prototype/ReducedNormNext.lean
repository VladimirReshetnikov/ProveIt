import DiophantineConsistency.ReducedNormBounds
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ReducedNormNext
open ReducedNormBounds

theorem ring_transform_v_ne_zero {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (r v a b s : R) (hr : 0<r) (hb : 0<b)
    (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) (hs : r=b*b*s) :
    let vp := (2*r+1)*v-2*b*s*a
    vp ≠ 0 := by
  dsimp only
  let vp := (2*r+1)*v-2*b*s*a
  let ap := (2*r+1)*a-2*(r+1)*v*b
  have hn0 : (r+1)*v*v*b*b-r*a*a-b*b=0 := by nlinarith [hn]
  have ht : (r+1)*vp*vp*b*b-r*ap*ap-b*b=0 := by
    rw [ring_transform_norm r v a b s hs, hn0]
  change vp ≠ 0
  intro hzero
  rw [hzero] at ht
  have hnon : 0≤r*(ap*ap) := mul_nonneg (le_of_lt hr) (by simpa only [pow_two] using sq_nonneg ap)
  have hpos : 0<b*b := mul_pos hb hb
  nlinarith
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_smaller_first {r v a b : V} (hr : 0<r) (hv : 1<v) (hb : 0<b)
    (hu : Bez a b 1) (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) :
    ∃ s k : V, r=(b*b)*s ∧ 0<k ∧ k<v ∧
      (let vp : DiffRing V := (2*ι r+1)*ι v-2*ι b*ι s*ι a
       (ι k=vp ∨ ι k= -vp)) := by
  obtain ⟨s,hs,_,_⟩ := model_bounds hr hv hb hu hn
  have hr' : (0:DiffRing V)<ι r := by simpa using (ι_lt_ι (a:=0) (b:=r)).mpr hr
  have hv' : (1:DiffRing V)<ι v := by simpa using (ι_lt_ι (a:=1) (b:=v)).mpr hv
  have hb' : (0:DiffRing V)<ι b := by simpa using (ι_lt_ι (a:=0) (b:=b)).mpr hb
  have hn' : (ι r+1)*(ι v*ι b)*(ι v*ι b)=ι r*(ι a*ι a)+ι b*ι b := by
    simpa only [map_add,map_mul,map_one] using congrArg (fun x : V => ι x) hn
  have hs' : ι r=ι b*ι b*ι s := by
    simpa only [map_mul] using congrArg (fun x : V => ι x) hs
  let vp : DiffRing V := (2*ι r+1)*ι v-2*ι b*ι s*ι a
  have hinterval : (-ι v<vp) ∧ (vp<ι v) :=
    ring_transform_interval (ι r) (ι v) (ι a) (ι b) (ι s) hr' hv' (ι_nonneg a) hb' hn' hs'
  have hne : vp≠0 := ring_transform_v_ne_zero (ι r) (ι v) (ι a) (ι b) (ι s) hr' hb' hn' hs'
  rcases nonneg_or_nonpos vp with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hkpos : 0<k := by
      by_contra hnpos
      have hk0 : k=0 := le_antisymm (le_of_not_gt hnpos) (Arithmetic.zero_le k)
      apply hne
      simpa only [hk0,map_zero] using hk
    have hklt : k<v := (ι_lt_ι (a:=k) (b:=v)).mp (by simpa only [←hk] using hinterval.2)
    exact ⟨s,k,hs,hkpos,hklt,Or.inl hk.symm⟩
  · have hkpos : 0<k := by
      by_contra hnpos
      have hk0 : k=0 := le_antisymm (le_of_not_gt hnpos) (Arithmetic.zero_le k)
      apply hne
      simpa only [hk0,map_zero,neg_zero] using hk
    have hklt : k<v := by
      apply (ι_lt_ι (a:=k) (b:=v)).mp
      have h : -ι v < -ι k := by simpa only [hk] using hinterval.1
      exact neg_lt_neg_iff.mp h
    refine ⟨s,k,hs,hkpos,hklt,Or.inr ?_⟩
    change ι k= -vp
    rw [hk]; simp

end ReducedNormNext
#print axioms ReducedNormNext.ring_transform_v_ne_zero

#print axioms ReducedNormNext.model_smaller_first
