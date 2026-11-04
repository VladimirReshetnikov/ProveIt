import Trace74UniformProjectionGraph
import Trace74UniformQuotientSize
import Trace74N8R11HeightModel

/-! Same-zero exclusion for first index 8 and main index 11. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N8R11GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74UniformProjectionGraph Trace74N8R11HeightModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_nine : Exp.exp (9:V)=512 := by
  have h2 : power (2:V) 2=4 := by
    rw [show (2:V)=1+1 by norm_num,power_succ,power_one]
    norm_num
  have h4 : power (2:V) 4=16 := by
    rw [show (4:V)=2+2 by norm_num,power_add,h2]
    norm_num
  have h8 : power (2:V) 8=256 := by
    rw [show (8:V)=4+4 by norm_num,power_add,h4]
    norm_num
  rw [←power_two,show (9:V)=8+1 by norm_num,power_succ,h8]
  norm_num

/-- The first-8 and main-11 ordinate identities cannot hold for one
positive large-q graph zero. -/
theorem graph_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hq : (1073741824:V)≤q p v)
    (hfirst : 2*ycoord 8 (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 11 (A p v-1)) : False := by
  have hqpos : 0<q p v := lt_of_lt_of_le (by norm_num) hq
  have hY : (q p v)*(q p v)*(q p v)≤Y p v := by
    have hm := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6))
      (show (0:V)≤q p v*q p v*q p v by simp)
    simpa only [mul_one,Y,mul_assoc] using hm
  have hY1 : (1:V)≤Y p v := pos_iff_one_le.mp (lt_of_lt_of_le (by positivity) hY)
  have hh : b p v<q p v := by
    change b p v<b p v+1
    exact lt_add_of_pos_right _ (by norm_num)
  have hq2 : (512:V)≤q p v*q p v := by
    have hm := mul_le_mul hq hq (by simp : (0:V)≤(1073741824:V)) (by simp : (0:V)≤q p v)
    exact le_trans (by norm_num) hm
  have h512h : 512*(b p v)<Y p v := calc
    _<512*(q p v) := mul_lt_mul_of_pos_left hh (by norm_num)
    _≤(q p v*q p v)*q p v := mul_le_mul_of_nonneg_right hq2 (by simp)
    _≤Y p v := hY
  have hsize := tuple_height p v hq hv hfirst hmain
  let h : DiffRing V := ι (b p v)
  let x : DiffRing V := ι (X p v)
  let y : DiffRing V := ι (Y p v)
  have hdisc : ∀ t : DiffRing V, 0<t → 1≤t := fun _ ht => one_le_of_pos (fun _ hu => pos_iff_one_le.mp hu) ht
  have hhpos : 0<h := by
    dsimp [h,b]
    simpa only [map_zero] using (ι_lt_ι.mpr (mul_pos hb (hv 0)))
  have hy1 : 1≤y := by dsimp [y]; simpa only [map_one] using (ι_le_ι.mpr hY1)
  have hLh : (512:DiffRing V)*h<y := by
    dsimp [h,y]
    simpa only [map_mul,map_ofNat] using (ι_lt_ι.mpr h512h)
  have hx : 8*h*(4*(512:DiffRing V))^2*y<x := by
    dsimp [h,x,y]
    have hm := ι_lt_ι.mpr hsize
    simp only [map_mul,map_ofNat] at hm
    convert hm using 1
    all_goals ring
  have hd := graph_reduced p v 11 hb hv hz (by norm_num) hmain
  have hs : (11:V)-2=9 := by
    apply add_right_cancel (b := (2:V))
    calc
      (11:V)-2+2=11 := tsub_add_cancel_of_le (by norm_num)
      _=9+2 := by norm_num
  rw [hs,exp_nine] at hd
  simp only [map_ofNat] at hd
  change (4*y*(x+1)-1) ∣ h*(4*y-1)*(4*(4*(512:DiffRing V)+1)*y-1)*
    ((4*(512:DiffRing V)-1)*y-512) at hd
  exact Trace74UniformQuotientSize.impossible h x y 512 hdisc hhpos hy1 (by norm_num) hLh hx hd

#print axioms Trace74N8R11GraphExclusion.graph_impossible
end Trace74N8R11GraphExclusion
