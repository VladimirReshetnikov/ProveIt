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
  let vp := (2*r+1)*v-2*b*s*a
  let ap := (2*r+1)*a-2*(r+1)*v*b
  have hn0 : (r+1)*v*v*b*b-r*a*a-b*b=0 := by nlinarith [hn]
  have ht : (r+1)*vp*vp*b*b-r*ap*ap-b*b=0 := by
    rw [ring_transform_norm r v a b s hs, hn0]
  intro hzero
  rw [hzero] at ht
  have hnon : 0≤r*(ap*ap) := mul_nonneg (le_of_lt hr) (sq_nonneg ap)
  have hpos : 0<b*b := mul_pos hb hb
  nlinarith
end ReducedNormNext
#print axioms ReducedNormNext.ring_transform_v_ne_zero
