import Trace74N4R7ScalarDiscrete
import Trace74N4OddSeven
import Trace74N4R7PellIdentity
import Trace74N4R5GraphExclusion

/-! UNCHECKED DRAFT. Same-tuple n=4 graph contradiction via r=7 interval. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74N4OddSeven Trace74N4R7PellIdentity Trace74N4R5GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_four_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord 4 (2*(firstParam p v-1)+1)=k v) : False := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hj1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
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
  have hA2 : A p v-1+2=A p v+1 := by
    rw [show A p v-1+2=(A p v-1+1)+1 by ring,hA1]
  have hc7 := graph_first_four_odd_seven p v hb31 hv hz hcoord
  have hy7 := ordinate_seven (A p v-1)
  rw [hA2,hA] at hy7
  have hy7R := congrArg (fun z : V => (ι z:DiffRing V)) hy7
  simp only [map_add,map_mul,map_pow,map_ofNat,map_one] at hy7R
  have hlo : k v*Y p v<c p v := by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ (hv 8)
  have hη : v 8<k v := by
    change v 8<v 8+v 9
    exact lt_add_of_pos_right _ (hv 9)
  have hhi : c p v<k v*(Y p v+1) := by
    change k v*Y p v+v 8<k v*(Y p v+1)
    have hh := add_lt_add_left hη (k v*Y p v)
    simpa only [mul_add,mul_one,add_comm] using hh
  have hkR : (ι (k v):DiffRing V)=Trace74N4R7ScalarDiscrete.k (ι (X p v)) (2*ι (Y p v)) := by
    rw [hk]
    dsimp [P,firstParam,Trace74N4R7ScalarDiscrete.k]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    ring
  have hkyR : (ι (k v*Y p v):DiffRing V)=Trace74N4R7ScalarDiscrete.ky (ι (X p v)) (2*ι (Y p v)) := by
    rw [hk]
    dsimp [P,firstParam,Trace74N4R7ScalarDiscrete.ky]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    ring
  have hcR : (ι (c p v):DiffRing V)=Trace74N4R7ScalarDiscrete.c (ι (X p v)) (2*ι (Y p v)) := by
    rw [hc7,hA]
    dsimp [Trace74N4R7ScalarDiscrete.c]
    linear_combination hy7R
  have hhiR : Trace74N4R7ScalarDiscrete.c (ι (X p v)) (2*ι (Y p v)) <
      Trace74N4R7ScalarDiscrete.ky (ι (X p v)) (2*ι (Y p v))+
        Trace74N4R7ScalarDiscrete.k (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hcR,←hkyR,←hkR]
    simpa only [map_mul,map_add,map_one,mul_add,mul_one] using (ι_lt_ι.mpr hhi)
  have hloR : Trace74N4R7ScalarDiscrete.ky (ι (X p v)) (2*ι (Y p v)) <
      Trace74N4R7ScalarDiscrete.c (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hkyR,←hcR]
    exact ι_lt_ι.mpr hlo
  apply Trace74N4R7ScalarDiscrete.no_scalar_solution (ι (q p v)) (ι (X p v)) (ι (Y p v)) (ι (v 5)) (ι (v 6))
  · intro z hz
    exact ModelDifferenceRing.one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hz
  · simpa only [map_ofNat] using (ι_le_ι.mpr hq32)
  · simpa only [map_ofNat] using (ι_le_ι.mpr hX32)
  · simpa only [map_one] using (ι_le_ι.mpr hY1)
  · simp only [X,map_mul]; ring
  · simp only [Y,map_mul]; ring
  · exact hloR
  · exact hhiR

#print axioms Trace74N4GraphExclusion.graph_first_four_impossible
end Trace74N4GraphExclusion
