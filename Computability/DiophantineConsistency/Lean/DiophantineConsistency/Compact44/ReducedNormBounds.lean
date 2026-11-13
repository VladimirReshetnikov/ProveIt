import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.Compact44.ModelSquareDivisor
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ReducedNormBounds

theorem ring_bounds {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (r v a b : R) (hr : 0<r) (hv : 1<v) (ha : 0≤a) (hb : 0<b)
    (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) :
    v*b<a ∧ r*a<(r+1)*v*b := by
  have hvb : b<v*b := by
    have h := mul_lt_mul_of_pos_right hv hb
    simpa only [one_mul] using h
  have hb0 : 0≤b := le_of_lt hb
  have hvb0 : 0≤v*b := le_trans hb0 (le_of_lt hvb)
  have hsq : b*b<(v*b)*(v*b) := by
    have hh := mul_self_lt_mul_self hb0 hvb
    exact hh
  have first : v*b<a := by
    by_contra hh
    have hal : a≤v*b := le_of_not_gt hh
    have hsqle : a*a ≤ (v*b)*(v*b) := mul_self_le_mul_self ha hal
    have hm := mul_le_mul_of_nonneg_left hsqle (le_of_lt hr)
    nlinarith [hn]
  have hid : ((r+1)*v*b)*((r+1)*v*b)=
      (r*a)*(r*a)+((r+1)*b*b+r*a*a) := by
    calc
      ((r+1)*v*b)*((r+1)*v*b)=(r+1)*((r+1)*(v*b)*(v*b)) := by ring
      _=(r+1)*(r*(a*a)+b*b) := by rw [hn]
      _=(r*a)*(r*a)+((r+1)*b*b+r*a*a) := by ring
  have hpos : 0<(r+1)*b*b+r*a*a := by positivity
  have hsq' : (r*a)*(r*a)<((r+1)*v*b)*((r+1)*v*b) := by
    rw [hid]
    exact lt_add_of_pos_right _ hpos
  have hsecond : r*a<(r+1)*v*b := by
    exact lt_of_mul_self_lt_mul_self₀ (by positivity) hsq'
  exact ⟨first,hsecond⟩

/-- The cleared transform preserves the reduced equation once the square
    divisor witness has actually been supplied. -/
theorem ring_transform_norm {R : Type*} [CommRing R]
    (r v a b s : R) (hs : r=b*b*s) :
    let vp := (2*r+1)*v-2*b*s*a
    let ap := (2*r+1)*a-2*(r+1)*v*b
    (r+1)*vp*vp*b*b-r*ap*ap-b*b = (r+1)*v*v*b*b-r*a*a-b*b := by
  dsimp only
  rw [hs]
  ring

/-- The signed first coordinate falls strictly between `-v` and `v`. -/
theorem ring_transform_interval {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (r v a b s : R) (hr : 0<r) (hv : 1<v) (ha : 0≤a) (hb : 0<b)
    (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) (hs : r=b*b*s) :
    let vp := (2*r+1)*v-2*b*s*a
    (-v < vp) ∧ (vp < v) := by
  obtain ⟨h1,h2⟩ := ring_bounds r v a b hr hv ha hb hn
  let vp := (2*r+1)*v-2*b*s*a
  have he1 : b*(v-vp)=2*r*(a-v*b) := by dsimp [vp]; rw [hs]; ring
  have he2 : b*(v+vp)=2*((r+1)*v*b-r*a) := by dsimp [vp]; rw [hs]; ring
  have hu : 0<b*(v-vp) := by
    rw [he1]
    exact mul_pos (mul_pos (by norm_num) hr) (sub_pos.mpr h1)
  have hl : 0<b*(v+vp) := by
    rw [he2]
    exact mul_pos (by norm_num) (sub_pos.mpr h2)
  have hu' : 0<v-vp := (mul_pos_iff_of_pos_left hb).mp hu
  have hl' : 0<v+vp := (mul_pos_iff_of_pos_left hb).mp hl
  constructor
  · linarith
  · exact sub_pos.mp hu'

/-- The signed numerator transform transports any supplied ring Bézout
    certificate. No gcd or integrality conclusion is assumed. -/
theorem ring_transform_bezout {R : Type*} [CommRing R]
    (r v a b s : R) (hs : r=b*b*s)
    (hu : ∃ x y : R, a*x+b*y=1) :
    let ap := (2*r+1)*a-2*(r+1)*v*b
    ∃ x y : R, ap*x+b*y=1 := by
  obtain ⟨x,y,hxy⟩ := hu
  let ap := (2*r+1)*a-2*(r+1)*v*b
  let t := 2*b*s*a-2*(r+1)*v
  have ht : ap-a=b*t := by dsimp [ap,t]; rw [hs]; ring
  refine ⟨x,y-t*x,?_⟩
  calc
    ap*x+b*(y-t*x)=(ap-b*t)*x+b*y := by ring
    _=a*x+b*y := by rw [←ht]; ring
    _=1 := hxy

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.ArithmeticGcdNormalization
open ModelSquareDivisor
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_bounds {r v a b : V} (hr : 0<r) (hv : 1<v) (hb : 0<b)
    (hu : Bez a b 1) (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) :
    ∃ s : V, r=(b*b)*s ∧ v*b<a ∧ r*a<(r+1)*v*b := by
  have hx : (r+1)*(v*v)*(b*b)=r*(a*a)+b*b := by calc
    (r+1)*(v*v)*(b*b)=(r+1)*(v*b)*(v*b) := by ring
    _=r*(a*a)+b*b := hn
  obtain ⟨s,hs⟩ := square_divisor_of_reduced_norm hu hx
  have hr' : (0:DiffRing V)<ι r := by simpa using (ι_lt_ι (a:=0) (b:=r)).mpr hr
  have hv' : (1:DiffRing V)<ι v := by simpa using (ι_lt_ι (a:=1) (b:=v)).mpr hv
  have hb' : (0:DiffRing V)<ι b := by simpa using (ι_lt_ι (a:=0) (b:=b)).mpr hb
  have hn' : (ι r+1)*(ι v*ι b)*(ι v*ι b)=ι r*(ι a*ι a)+ι b*ι b := by
    simpa only [map_add,map_mul,map_one] using congrArg (fun x : V => ι x) hn
  obtain ⟨h1,h2⟩ := ring_bounds (ι r) (ι v) (ι a) (ι b) hr' hv' (ι_nonneg a) hb' hn'
  refine ⟨s,hs,?_,?_⟩
  · apply (ι_lt_ι (a:=v*b) (b:=a)).mp
    simpa only [map_mul] using h1
  · apply (ι_lt_ι (a:=r*a) (b:=(r+1)*v*b)).mp
    simpa only [map_mul,map_add,map_one] using h2
theorem bez_iff_diff {a b : V} :
    Bez a b 1 ↔ ∃ x y : DiffRing V, ι a*x+ι b*y=1 := by
  constructor
  · rintro ⟨u,v,w,z,he⟩
    refine ⟨mk w u,mk z v,?_⟩
    rw [ι_apply,ι_apply,mk_mul,mk_mul,mk_add,one_def,mk_eq]
    simpa only [zero_mul,mul_zero,add_zero,zero_add,add_assoc] using he.symm
  · rintro ⟨x,y,he⟩
    obtain ⟨w,u,hx⟩ := exists_mk x
    obtain ⟨z,v,hy⟩ := exists_mk y
    rw [hx,hy,ι_apply,ι_apply,mk_mul,mk_mul,mk_add,one_def,mk_eq] at he
    refine ⟨u,v,w,z,?_⟩
    simpa only [zero_mul,mul_zero,add_zero,zero_add,add_assoc] using he.symm
/-- Construct the divisor witness and a reduced natural absolute numerator
    with an explicitly transported four-natural Bézout certificate. -/
theorem model_signed_numerator {r v a b : V} (hu : Bez a b 1)
    (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) :
    ∃ s t : V, r=(b*b)*s ∧
      (let ap : DiffRing V := (2*ι r+1)*ι a-2*(ι r+1)*ι v*ι b
       (ι t=ap ∨ ι t= -ap)) ∧ Bez t b 1 := by
  have hx : ((r+1)*(v*v))*(b*b)=r*(a*a)+b*b := by calc
    ((r+1)*(v*v))*(b*b)=(r+1)*(v*b)*(v*b) := by ring
    _=r*(a*a)+b*b := hn
  obtain ⟨s,hs⟩ := square_divisor_of_reduced_norm hu hx
  have hs' : ι r=ι b*ι b*ι s := by
    simpa only [map_mul] using congrArg (fun x : V => ι x) hs
  let ap : DiffRing V := (2*ι r+1)*ι a-2*(ι r+1)*ι v*ι b
  have hh : ∃ x y : DiffRing V, ap*x+ι b*y=1 :=
    ring_transform_bezout (ι r) (ι v) (ι a) (ι b) (ι s) hs' (bez_iff_diff.mp hu)
  rcases nonneg_or_nonpos ap with ⟨t,ht⟩ | ⟨t,ht⟩
  · refine ⟨s,t,hs,Or.inl ht.symm,?_⟩
    apply bez_iff_diff.mpr
    simpa only [ht] using hh
  · refine ⟨s,t,hs,Or.inr ?_,?_⟩
    · change ι t= -ap
      rw [ht]; simp
    · apply bez_iff_diff.mpr
      obtain ⟨x,y,hxy⟩ := hh
      refine ⟨-x,y,?_⟩
      rw [ht] at hxy
      calc
        ι t*(-x)+ι b*y=(-ι t)*x+ι b*y := by ring
        _=1 := hxy

end ReducedNormBounds
#print axioms ReducedNormBounds.ring_bounds
#print axioms ReducedNormBounds.model_bounds

#print axioms ReducedNormBounds.bez_iff_diff

#print axioms ReducedNormBounds.ring_transform_norm
#print axioms ReducedNormBounds.ring_transform_interval
#print axioms ReducedNormBounds.ring_transform_bezout

#print axioms ReducedNormBounds.model_signed_numerator
