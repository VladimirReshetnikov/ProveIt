import DiophantineConsistency.BFS943.CarrierTransport

/-! Sign-free offset estimate needed by the carrier contradiction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveOffsetBound
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem offset_bound (b c F2 e v m : K) (hc : 0<c) (hF : c+1<F2)
    (he : e<b) (hv : v=F2*b-c) (hm : 2≤m)
    (hdiscrete : 0<b → 1≤b) : 2*e<v*v*m := by
  by_cases hb : b≤0
  · have he0 : e<0 := lt_of_lt_of_le he hb
    have hnonneg : 0≤v*v*m := mul_nonneg (mul_self_nonneg v) (le_trans (by norm_num) hm)
    nlinarith only [he0,hnonneg]
  · have hbpos : 0<b := lt_of_not_ge hb
    have hb1 : 1≤b := hdiscrete hbpos
    have hvb : b<v := by
      have h := mul_pos (sub_pos.mpr hF) hbpos
      nlinarith only [h,hb1,hc,hv]
    have hv1 : 1≤v := le_trans hb1 (le_of_lt hvb)
    have h1 : 0≤v*(v-1) := mul_nonneg (le_trans (by norm_num) hv1) (sub_nonneg.mpr hv1)
    have h2 : 0≤v*v*(m-2) := mul_nonneg (mul_self_nonneg v) (sub_nonneg.mpr hm)
    nlinarith only [h1,h2,he,hvb]

#print axioms TenPositiveOffsetBound.offset_bound
end TenPositiveOffsetBound
