import Trace74N5R9ScalarDiscrete
import Trace74N5OddNine
import Trace74N5R9PellIdentity
import Trace74N2FifthGrowth
import Trace74Pell
import Mathlib.Tactic.LinearCombination

/-! UNCHECKED DRAFT. Exclude the same-tuple n=5 branch using main r=9. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N5GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74N5OddNine Trace74N5R9PellIdentity Trace74N2FifthGrowth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_five_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hqbig : (1073741824:V)≤q p v)
    (hcoord : 2*ycoord 5 (2*(firstParam p v-1)+1)=k v) : False := by
  have hq73 : (73:V)≤q p v := le_trans (by norm_num) hqbig
  have hq32 : (32:V)≤q p v := le_trans (by norm_num) hq73
  have hq : 0<q p v := lt_of_lt_of_le (by norm_num : (0:V)<32) hq32
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hX32 : (32:V)≤X p v := calc
    (32:V)≤q p v := hq32
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (show (0:V)≤q p v by simp)
    _=X p v := rfl
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB1 : B+1=2*P := by
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
  have hk : k v=2*(16*(2*P)^4+64*(2*P)^3+84*(2*P)^2+40*(2*P)+5) := by
    rw [←hcoord,ordinate_five,hB1]
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hApos : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hA2 : A p v-1+2=A p v+1 := by
    rw [show A p v-1+2=(A p v-1+1)+1 by ring,hA1]
  have hc9 := graph_first_five_odd_nine p v hb15 hv hz hqbig hcoord
  have hy9 := ordinate_nine (A p v-1)
  rw [hA2,hA] at hy9
  have hy9R := congrArg (fun z : V => (ι z:DiffRing V)) hy9
  simp only [map_add,map_mul,map_pow,map_ofNat,map_one] at hy9R
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
  have hkR : (ι (k v):DiffRing V)=Trace74N5R9ScalarDiscrete.k (ι (X p v)) (2*ι (Y p v)) := by
    rw [hk]
    dsimp [P,firstParam,Trace74N5R9ScalarDiscrete.k]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    ring
  have hkyR : (ι (k v*Y p v):DiffRing V)=Trace74N5R9ScalarDiscrete.ky (ι (X p v)) (2*ι (Y p v)) := by
    rw [hk]
    dsimp [P,firstParam,Trace74N5R9ScalarDiscrete.ky]
    simp only [map_add,map_mul,map_pow,map_ofNat]
    ring
  have hcR : (ι (c p v):DiffRing V)=Trace74N5R9ScalarDiscrete.c (ι (X p v)) (2*ι (Y p v)) := by
    rw [hc9,hA]
    dsimp [Trace74N5R9ScalarDiscrete.c]
    linear_combination hy9R
  have hhiR : Trace74N5R9ScalarDiscrete.c (ι (X p v)) (2*ι (Y p v)) <
      Trace74N5R9ScalarDiscrete.ky (ι (X p v)) (2*ι (Y p v))+
        Trace74N5R9ScalarDiscrete.k (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hcR,←hkyR,←hkR]
    simpa only [map_mul,map_add,map_one,mul_add,mul_one] using (ι_lt_ι.mpr hhi)
  have hloR : Trace74N5R9ScalarDiscrete.ky (ι (X p v)) (2*ι (Y p v)) <
      Trace74N5R9ScalarDiscrete.c (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hkyR,←hcR]
    exact ι_lt_ι.mpr hlo
  apply Trace74N5R9ScalarDiscrete.no_scalar_solution (ι (q p v)) (ι (X p v)) (ι (Y p v)) (ι (v 5)) (ι (v 6))
  · intro z hz'
    exact ModelDifferenceRing.one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hz'
  · simpa only [map_ofNat] using (ι_le_ι.mpr hq73)
  · simpa only [map_ofNat] using (ι_le_ι.mpr hX32)
  · simpa only [map_one] using (ι_le_ι.mpr hY1)
  · simp only [X,map_mul]; ring
  · simp only [Y,map_mul]; ring
  · exact hloR
  · exact hhiR

#print axioms Trace74N5GraphExclusion.graph_first_five_impossible
end Trace74N5GraphExclusion
