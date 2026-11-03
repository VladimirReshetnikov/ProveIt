import OffsetBound
import Trace75Residue

/-! Sign-free offset estimate for the actual trace75 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75OffsetBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Residue TenPositiveOffsetBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_offset_bound (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    2*(regs (ports p) (fun j => ι (v j))).e <
      ((regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V)*
      (regs (ports p) (fun j => ι (v j))).D := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let C : V := c p v
  let a : V := D*U0*U0*E0
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let R : DiffRing V := (regs (ports p) w).rank
  let B : DiffRing V := (regs (ports p) w).b
  let e : DiffRing V := (regs (ports p) w).e
  let vv : DiffRing V := (regs (ports p) w).V
  let FF : DiffRing V := ι (1+2*a)
  let mm : DiffRing V := (regs (ports p) w).D
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hC : 0<C := add_pos (mul_pos hk hY) (hv 8)
  have hCk : k v<C := lt_of_le_of_lt (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
  obtain ⟨hD,hU,hE,_hM⟩ := factors_positive p v hb hv
  have hC1 : 1≤C := pos_iff_one_le.mp hC
  have hU1 : 1≤U0 := pos_iff_one_le.mp hU
  have hCU : C≤U0 := by
    calc
      C≤C*C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hC1 (by simp : (0:V)≤C)
      _≤v 3*(C*C) := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 3))
      _=U0 := rfl
  have hUa : U0≤a := by
    calc
      U0≤D*U0 := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD)
      _≤D*U0*U0 := le_mul_of_one_le_right (by simp) hU1
      _≤D*U0*U0*E0 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hE)
      _=a := rfl
  have hCa : C≤a := le_trans hCU hUa
  have hCR : (0:DiffRing V)<ι C := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hC
  have hCaR : (ι C:DiffRing V)≤ι a := ι_le_ι.mpr hCa
  have hF : ι C+1<FF := by
    dsimp [FF]
    simp only [map_add,map_mul,map_one,map_ofNat]
    linarith
  have hT : (1:DiffRing V)≤ι (v 4) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
    exact pos_iff_one_le.mp (hv 4)
  have hCT : (ι C:DiffRing V)≤ι C*ι (v 4) := le_mul_of_one_le_right (le_of_lt hCR) hT
  have hCkR : (ι (k v):DiffRing V)<ι C := ι_lt_ι.mpr hCk
  have eeval : e=ι (k v)-R-1 := by
    dsimp [e,R,w]
    rw [e_def,k_def]
    simp only [k,map_add]
  have beval : B=ι C*ι (v 4)-R := by
    dsimp [B,R,w]
    rw [b_def,c_eval]
  have hEB : e<B := by rw [eeval,beval]; linarith
  have hV : vv=FF*B-ι C := by
    dsimp [vv,FF,B,w]
    rw [V_def,f_eq,a_eq,delta_eval,U_eval,E_eval,c_eval]
    dsimp [a,D,U0,E0,C]
    simp only [pow_two,map_mul,map_add,map_one,map_ofNat]
    ring
  have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
  have hq2 : 2≤q p v := by
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hX2 : 2≤X p v := le_trans hq2 (by
    change q p v≤v 5*q p v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (show (0:V)≤q p v by simp))
  have hXY : 2≤X p v*Y p v := le_trans hX2
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hY))
  have hmval : mm=ι (X p v*Y p v) := by
    dsimp [mm,w]
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hmm : (2:DiffRing V)≤mm := by
    rw [hmval,←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
    exact hXY
  exact offset_bound B (ι C) FF e vv mm hCR hF hEB hV hmm
    (fun h => one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) h)

#print axioms Trace75OffsetBound.graph_offset_bound
end Trace75OffsetBound
