import Trace74R5NoSmallDivisor
import Trace74R5GraphProjection
import Trace74N2FifthGrowth
import Trace74Pell

/-! UNCHECKED DRAFT. Same-tuple n=4, r=5 graph contradiction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R5GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74R5GraphProjection Trace74N2FifthGrowth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinate_four_identity (B : V) :
    ycoord 4 B+4*(B+2)=8*(B+2)^3 := by
  have hx1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
  have hy1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
  have hx2 : xcoord 2 B=(B+2)*xcoord 1 B+ArithmeticPellRecurrence.delta B*ycoord 1 B := by
    simpa only [show (1:V)+1=2 by ring] using x_succ (1:V) B
  have hy2 : ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
    simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
  have hx3 : xcoord 3 B=(B+2)*xcoord 2 B+ArithmeticPellRecurrence.delta B*ycoord 2 B := by
    simpa only [show (2:V)+1=3 by ring] using x_succ (2:V) B
  have hy3 : ycoord 3 B=xcoord 2 B+(B+2)*ycoord 2 B := by
    simpa only [show (2:V)+1=3 by ring] using y_succ (2:V) B
  have hy4 : ycoord 4 B=xcoord 3 B+(B+2)*ycoord 3 B := by
    simpa only [show (3:V)+1=4 by ring] using y_succ (3:V) B
  rw [hy4,hx3,hy3,hx2,hy2,hx1,hy1]
  unfold ArithmeticPellRecurrence.delta
  ring

theorem graph_n4_r5_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord 4 (2*(firstParam p v-1)+1)=k v)
    (hc5 : c p v=ycoord 5 (A p v-1)) : False := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hj1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hs1 : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hq32 : (32:V)≤q p v := by
    unfold q b
    calc
      (32:V)=31*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb31 hj1 (by simp) (by simp)) 1
  have hX32 : (32:V)≤X p v := calc
    (32:V)≤q p v := hq32
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hYq : (q p v)^3≤Y p v := by
    change (q p v)^3≤(q p v*q p v*q p v)*v 6
    simpa only [pow_succ,pow_two,pow_zero,one_mul,mul_one] using
      mul_le_mul_of_nonneg_left hs1 (show (0:V)≤q p v*q p v*q p v by simp)
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  have hk : k v=128*P^3+192*P^2+80*P+8 := by
    have hy4 := ordinate_four_identity B
    apply add_right_cancel (b:=8*(2*P+1))
    calc
      k v+8*(2*P+1)=2*(ycoord 4 B+4*(B+2)) := by rw [←hcoord,←hB]; ring
      _=2*(8*(B+2)^3) := by rw [hy4]
      _=(128*P^3+192*P^2+80*P+8)+8*(2*P+1) := by rw [hB]; ring
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hApos : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hc : c p v=16*(A p v)^4+64*(A p v)^3+84*(A p v)^2+40*(A p v)+5 := by
    rw [hc5,ordinate_five,hA1]
  have hlo : k v*Y p v<c p v := by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ (hv 8)
  have hgap : (128*(ι (X p v)*(ι (Y p v))^2)^3+192*(ι (X p v)*(ι (Y p v))^2)^2+80*(ι (X p v)*(ι (Y p v))^2)+8)*ι (Y p v) <
      16*(ι (Y p v)*(ι (X p v)+1)+1)^4-12*(ι (Y p v)*(ι (X p v)+1)+1)^2+1 := by
    have hh := ι_lt_ι.mpr hlo
    rw [hk,hc,hA] at hh
    dsimp [P,firstParam] at hh
    simp only [map_add,map_mul,map_pow,map_ofNat,map_one] at hh
    convert hh using 1 <;> ring
  have hxR : (32:DiffRing V)≤ι (X p v) := by simpa only [map_ofNat] using (ι_le_ι.mpr hX32)
  have hyR : (1:DiffRing V)≤ι (Y p v) := by simpa only [map_one] using (ι_le_ι.mpr hY1)
  have hqR : (32:DiffRing V)≤ι (q p v) := by simpa only [map_ofNat] using (ι_le_ι.mpr hq32)
  have hyqR : (ι (q p v):DiffRing V)^3≤ι (Y p v) := by
    simpa only [map_pow] using (ι_le_ι.mpr hYq)
  have hxlarge := Trace74N4R5ScalarGrowth.x_gt_four_y_cube (ι (X p v)) (ι (Y p v)) hxR hyR hgap
  have hp := graph_r5_reduced p v hb hv hz hc5
  have hbq : (ι (b p v):DiffRing V)=ι (q p v)-1 := by simp only [q,map_add,map_one]; ring
  rw [hbq] at hp
  exact Trace74R5NoSmallDivisor.impossible (ι (q p v)) (ι (X p v)) (ι (Y p v))
    (fun z hz => ModelDifferenceRing.one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hz)
    hqR hyqR hxlarge hp

#print axioms Trace74N4R5GraphExclusion.ordinate_four_identity
#print axioms Trace74N4R5GraphExclusion.graph_n4_r5_impossible
end Trace74N4R5GraphExclusion
