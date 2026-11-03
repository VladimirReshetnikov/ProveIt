import DiophantineConsistency.ModelRatioBounds

/-! A strict whole-product height bound recovers X without cancelling b. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75ProductHeight
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ModelRatio
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem small_divisible_zero {J x : DiffRing V} (hJ : 0<J) (hd : J∣x)
    (h1 : x<J) (h2 : -J<x) : x=0 := by
  obtain ⟨k,rfl⟩ := hd
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exfalso
    have hk1 : (1:DiffRing V)≤ -k := one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) (neg_pos.mpr hk)
    have h3 : J*1≤J*(-k) := mul_le_mul_of_nonneg_left hk1 (le_of_lt hJ)
    linarith
  · rw [hk,mul_zero]
  · exfalso
    have hk1 : (1:DiffRing V)≤k := one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hk
    have h3 : J*1≤J*k := mul_le_mul_of_nonneg_left hk1 (le_of_lt hJ)
    linarith

theorem equality_of_height (b X t H : V) (hb : 0<b)
    (hheight : b*(X+t)*(t*X+1)<H)
    (hdiv : (ι H:DiffRing V) ∣ ι b*(ι X-ι t)*(ι t*ι X+1)) : X=t := by
  let P : DiffRing V := ι b*(ι X-ι t)*(ι t*ι X+1)
  have hbR : 0<(ι b:DiffRing V) := by simpa only [map_zero] using ι_lt_ι.mpr hb
  have hlast : 0<(ι t:DiffRing V)*ι X+1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (ι_nonneg t) (ι_nonneg X)) (by norm_num)
  have hdiff : |(ι X:DiffRing V)-ι t|≤ι (X+t) := by
    calc
      |(ι X:DiffRing V)-ι t|≤|ι X|+|ι t| := abs_sub _ _
      _=ι (X+t) := by rw [abs_of_nonneg (ι_nonneg X),abs_of_nonneg (ι_nonneg t),map_add]
  have hbound : |P|≤ι (b*(X+t)*(t*X+1)) := by
    dsimp [P]
    rw [abs_mul,abs_mul,abs_of_pos hbR,abs_of_pos hlast]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (le_of_lt hbR)) (le_of_lt hlast)
    simpa only [map_add,map_mul,map_one] using h
  have hH : 0<H := lt_of_le_of_lt (by simp) hheight
  have hHR : 0<(ι H:DiffRing V) := by simpa only [map_zero] using ι_lt_ι.mpr hH
  have habs : |P|<(ι H:DiffRing V) := lt_of_le_of_lt hbound (ι_lt_ι.mpr hheight)
  have hsmall := abs_lt.mp habs
  have hz : P=0 := small_divisible_zero hHR hdiv hsmall.2 hsmall.1
  have hmul : (ι b:DiffRing V)*((ι X:DiffRing V)-ι t)=0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hlast)
  have hsub : (ι X:DiffRing V)-ι t=0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hbR)
  exact ι_injective (sub_eq_zero.mp hsub)

#print axioms Trace75ProductHeight.equality_of_height
end Trace75ProductHeight
