import Trace74N3ScalarDiscrete
import Trace74N3OddFive
import Trace74N2FifthGrowth
import Trace74OddOrdinateBound

/-! UNCHECKED DRAFT. Bind the n=3 Pell polynomials and scalar contradiction
    to the same actual positive 74 graph tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N3GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74N3OddFive Trace74N2FifthGrowth Trace74OddOrdinateBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_three_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord 3 (2*(firstParam p v-1)+1)=k v) : False := by
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
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
  have hk : k v=32*P^2+32*P+6 := by
    have hy3 : 2*ycoord 3 B=32*P^2+32*P+6 := by
      apply add_right_cancel (b:=2)
      calc
        2*ycoord 3 B+2=2*(ycoord 3 B+1) := by ring
        _=2*(4*(B+2)^2) := by rw [ordinate_three]
        _=(32*P^2+32*P+6)+2 := by rw [hB]; ring
    exact hcoord.symm.trans hy3
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hApos : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hc5 := graph_first_three_odd_five p v hb15 hv hz hcoord
  have hc : c p v=16*(A p v)^4+64*(A p v)^3+84*(A p v)^2+40*(A p v)+5 := by
    rw [hc5,ordinate_five,hA1]
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
  have hkr : (ι (k v):DiffRing V)=Trace74FirstThreeLower.k (ι (X p v)) (ι (Y p v)) := by
    rw [hk]
    dsimp [P,firstParam,Trace74FirstThreeLower.k]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    ring
  have hcr : (ι (c p v):DiffRing V)=Trace74FirstThreeLower.c (ι (X p v)) (ι (Y p v)) := by
    rw [hc,hA]
    dsimp [Trace74FirstThreeLower.c]
    simp only [map_add,map_mul,map_pow,map_ofNat,map_one]
    ring
  apply Trace74N3ScalarDiscrete.no_scalar_solution (ι (q p v)) (ι (X p v)) (ι (Y p v)) (ι (v 5)) (ι (v 6))
  · intro z hz
    exact ModelDifferenceRing.one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hz
  · simpa only [map_ofNat] using (ι_le_ι.mpr hq32)
  · simpa only [map_ofNat] using (ι_le_ι.mpr hX32)
  · simpa only [map_one] using (ι_le_ι.mpr hY1)
  · simp only [X,map_mul]; ring
  · simp only [Y,map_mul]; ring
  · rw [←hkr,←hcr,←map_mul]; exact ι_lt_ι.mpr hlo
  · rw [←hkr,←hcr,←map_one (ι : V →+* DiffRing V),←map_add,←map_mul]; exact ι_lt_ι.mpr hhi

#print axioms Trace74N3GraphExclusion.graph_first_three_impossible
end Trace74N3GraphExclusion
