import Trace74N6R9Scalar
import Trace74N6FirstPellIdentity
import Trace74N5R9PellIdentity
import Trace74Pell
import Mathlib.Tactic.LinearCombination

/-! UNCHECKED DRAFT. Exclude n=6/r=9 for the same positive 74 tuple; no zero assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R9GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74N6FirstPellIdentity Trace74N5R9PellIdentity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_n6_r9_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hv : ∀j,0<v j) (hq32 : (32:V)≤q p v)
    (hcoord : 2*ycoord 6 (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 9 (A p v-1)) : False := by
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
  have hB2 : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  have hy6 := ordinate_six B
  rw [hB2] at hy6
  have hy6R := congrArg (fun z : V => (ι z:DiffRing V)) hy6
  simp only [map_add,map_mul,map_pow,map_ofNat,map_one] at hy6R
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hApos : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hA2 : A p v-1+2=A p v+1 := by
    rw [show A p v-1+2=(A p v-1+1)+1 by ring,hA1]
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
  have hkR : (ι (k v):DiffRing V)=2*Trace74N6R9Scalar.y6 (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hcoord]
    simp only [map_mul,map_ofNat]
    dsimp [Trace74N6R9Scalar.y6,B,P,firstParam] at hy6R ⊢
    simp only [map_mul] at hy6R
    linear_combination 2*hy6R
  have hkyR : (ι (k v*Y p v):DiffRing V)=(2*ι (Y p v))*Trace74N6R9Scalar.y6 (ι (X p v)) (2*ι (Y p v)) := by
    simp only [map_mul,hkR]
    ring
  have hcR : (ι (c p v):DiffRing V)=Trace74N6R9Scalar.c (ι (X p v)) (2*ι (Y p v)) := by
    rw [hmain,hA]
    dsimp [Trace74N6R9Scalar.c]
    linear_combination hy9R
  have hloR : (2*ι (Y p v))*Trace74N6R9Scalar.y6 (ι (X p v)) (2*ι (Y p v)) <
      Trace74N6R9Scalar.c (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hkyR,←hcR]
    exact ι_lt_ι.mpr hlo
  have hhiR : Trace74N6R9Scalar.c (ι (X p v)) (2*ι (Y p v)) <
      (2*ι (Y p v))*Trace74N6R9Scalar.y6 (ι (X p v)) (2*ι (Y p v))+
        2*Trace74N6R9Scalar.y6 (ι (X p v)) (2*ι (Y p v)) := by
    rw [←hcR,←hkyR,←hkR]
    simpa only [map_mul,map_add,map_one,mul_add,mul_one] using (ι_lt_ι.mpr hhi)
  apply Trace74N6R9Scalar.no_scalar_solution (ι (X p v)) (2*ι (Y p v))
  · intro z hz'
    exact ModelDifferenceRing.one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hz'
  · simpa only [map_ofNat] using (ι_le_ι.mpr hX32)
  · have hh := ι_le_ι.mpr hY1
    simp only [map_one] at hh
    linarith
  · exact hloR
  · exact hhiR

#print axioms Trace74N6R9GraphExclusion.graph_n6_r9_impossible
end Trace74N6R9GraphExclusion
