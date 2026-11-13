import Trace74AtLeastSevenR9Growth
import Trace74N4R7PellIdentity
import Trace74N5R9PellIdentity
import Trace74Pell
import DiophantineConsistency.ArithmeticPellCongruences

/-! Unchecked same-tuple model binding; ordinate and q bounds remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74AtLeastSevenR9ModelGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences Trace75Factors Trace74Pell
open Trace74N4R7PellIdentity Trace74N5R9PellIdentity Trace74AtLeastSevenR9Growth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem same_tuple_growth (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hqbig : (64:V)≤q p v) (hv : ∀j,0<v j)
    (hn : 7≤n) (hfirst : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 9 (A p v-1)) :
    (1048572*(ι (b p v))*(ι (Y p v)) : DiffRing V)<ι (X p v) := by
  have hq : 0<q p v := lt_of_lt_of_le (by norm_num : (0:V)<64) hqbig
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hs1 : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hq32 : (32:V)≤q p v := le_trans (by norm_num) hqbig
  have hX32 : (32:V)≤X p v := calc
    (32:V)≤q p v := hq32
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hYq : (q p v)^3≤Y p v := by
    have hh := mul_le_mul_of_nonneg_left hs1 (show (0:V)≤(q p v)^3 by simp)
    simpa only [mul_one,Y,pow_succ,pow_zero,one_mul,mul_assoc] using hh
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB2 : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  let K7 : V := 2*ycoord 7 B
  have hKle : K7≤k v := by
    dsimp [K7,B,P]
    rw [←hfirst]
    exact mul_le_mul_of_nonneg_left ((y_strictMono _).monotone hn) (by simp)
  have hy7B := ordinate_seven B
  rw [hB2] at hy7B
  have hy7BR := congrArg (fun z : V => (ι z:DiffRing V)) hy7B
  simp only [map_add,map_mul,map_pow,map_ofNat,map_one] at hy7BR
  dsimp [P,firstParam] at hy7BR
  simp only [map_mul] at hy7BR
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hApos : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hA2 : A p v-1+2=A p v+1 := by
    rw [show A p v-1+2=(A p v-1+1)+1 by ring,hA1]
  have hy9 := ordinate_nine (A p v-1)
  rw [hA2,hA] at hy9
  have hy9R := congrArg (fun z : V => (ι z:DiffRing V)) hy9
  simp only [map_add,map_mul,map_pow,map_ofNat,map_one] at hy9R
  have hlo0 : k v*Y p v<c p v := by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ (hv 8)
  have hlo : K7*Y p v<c p v :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hKle (le_of_lt hY)) hlo0
  let x : DiffRing V := ι (X p v)
  let y : DiffRing V := ι (Y p v)
  let t : DiffRing V := 2*y
  have hkR : (ι (K7*Y p v):DiffRing V)=t*((x*t^2+2)^6-5*(x*t^2+2)^4+6*(x*t^2+2)^2-1) := by
    dsimp [K7,x,y,t]
    simp only [map_mul,map_ofNat]
    linear_combination 2*(ι (Y p v))*hy7BR
  have hcR : (ι (c p v):DiffRing V)=(t*(x+1)+2)^8-7*(t*(x+1)+2)^6+15*(t*(x+1)+2)^4-10*(t*(x+1)+2)^2+1 := by
    rw [hmain,hA]
    dsimp [x,y,t]
    linear_combination hy9R
  have hgap : t*((x*t^2+2)^6-5*(x*t^2+2)^4+6*(x*t^2+2)^2-1) <
      (t*(x+1)+2)^8-7*(t*(x+1)+2)^6+15*(t*(x+1)+2)^4-10*(t*(x+1)+2)^2+1 := by
    rw [←hkR,←hcR]
    exact ι_lt_ι.mpr hlo
  have hx32 : (32:DiffRing V)≤x := by simpa only [x,map_ofNat] using (ι_le_ι.mpr hX32)
  have ht2 : (2:DiffRing V)≤t := by
    have hh := ι_le_ι.mpr hY1
    dsimp [t,y]
    simp only [map_one] at hh
    linarith
  have hsq := squared_growth x t hx32 ht2 hgap
  have hg : 16*y^5<x^2 := by dsimp [t] at hsq; nlinarith
  have hbig : (64:DiffRing V)≤ι (q p v) := by
    simpa only [map_ofNat] using (ι_le_ι.mpr hqbig)
  have hyqR : (ι (q p v):DiffRing V)^3≤y := by
    simpa only [y,map_pow] using (ι_le_ι.mpr hYq)
  have hsize := large_size (ι (q p v)) x y hbig hx32 hyqR hg
  have hb : (ι (q p v):DiffRing V)-1=ι (b p v) := by
    simp only [q,map_add,map_one]
    ring
  rw [hb] at hsize
  exact hsize

#print axioms Trace74AtLeastSevenR9ModelGrowth.same_tuple_growth
end Trace74AtLeastSevenR9ModelGrowth
