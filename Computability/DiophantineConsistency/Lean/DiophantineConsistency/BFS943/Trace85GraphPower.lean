import DiophantineConsistency.BFS943.Trace85VariableHeight
import DiophantineConsistency.BFS943.Trace87ProductPower
import DiophantineConsistency.BFS943.Trace75ProductHeight

/-! # Exact power recovery `X = 2^R` for the 85/232 circuit

`Trace87GraphPower.graph_power` for the 85 registers: the height bound
(`Trace85VariableHeight`) and the whole-product projection with multiplier
`6 h X` (`Trace85Projection`). The literal factor `6` of `D = 6 q⁶` is
absorbed by the cube-multiplier bound
`Trace87ProductPower.whole_product_lt_power_cube` (`6 h X ≤ X³`, `r ≥ 25`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace85GraphPower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace85
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticPow
open Trace85Factors Trace85NormRank Trace85VariableHeight

theorem graph_power (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value85 (ports p) (fun j => ι (v j)) = 0) :
    X p v=Exp.exp (rankNat p v) := by
  let rr := regs (ports p) (fun j => ι (v j))
  obtain ⟨hzn,hm,hq4⟩ := Trace85Projection.zero_norm_data p v hb31 hv hz
  let R : V := rankNat p v
  let X0 : V := X p v
  let b0 : V := b p v
  let H : V := Hnat p v
  let T : V := Exp.exp R
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hb0 : 0<b0 := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X0 := mul_pos hq (hv 5)
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hq32 : (32:V)≤q p v := by
    unfold q b
    calc
      (32:V)=31*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb31 hj (by simp) (by simp)) 1
  have hqX : q p v≤X0 :=
    le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 5))
  have hX32 : (32:V)≤X0 := le_trans hq32 hqX
  have hbX : b0≤X0 := le_trans (show b0≤q p v by dsimp [b0,q]; simp) hqX
  have hbXX : 6*b0*X0≤X0*X0*X0 := by
    have h6 : 6*b0≤X0*X0 := calc
      6*b0≤6*X0 := mul_le_mul_of_nonneg_left hbX (by simp)
      _≤X0*X0 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) hX32) (by simp)
    exact mul_le_mul_of_nonneg_right h6 (by simp)
  obtain ⟨r,_hrpos,hR,_hsmall,hheight⟩ := graph_variable_height p v hb31 hl hh hv hz
  change R=2*r+1 at hR
  change power X0 (r+1)<H at hheight
  have h41 : (51:V)≤R := le_trans (by norm_num : (51:V)≤3*32)
    (le_trans (mul_le_mul_of_nonneg_left hq32 (by simp)) (le_of_lt (graph_rank_exact p v _ hb31 hl hh hv hzn hm).2.1))
  have hr20 : (25:V)≤r := by
    have h2 : (2:V)*25≤2*r := (add_le_add_iff_right (1:V)).mp (by
      simpa only [show (2:V)*25+1=51 by ring,←hR] using h41)
    exact le_of_mul_le_mul_left h2 (by norm_num : (0:V)<2)
  have hproduct : (6*b0*X0)*(X0+T)*(T*X0+1)<H := calc
    (6*b0*X0)*(X0+T)*(T*X0+1)<power X0 (r+1) := by
      simpa only [T,hR] using Trace87ProductPower.whole_product_lt_power_cube X0 (6*b0*X0) r hX32 hbXX hr20
    _<H := hheight
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have h4A : 1≤4*A p v := le_trans (pos_iff_one_le.mp hA) (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:V)≤4) (by simp : (0:V)≤A p v))
  have hH1 : H+1=4*A p v := tsub_add_cancel_of_le h4A
  have hAeval : rr.Am1=ι (A p v) := by
    dsimp [rr,A,X,Y,q,b,ports]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have hHcast : rr.H=ι H := by
    have he : (ι H:DiffRing V)+1=4*ι (A p v) := by
      rw [←map_one (ι : V →+* DiffRing V),←map_add,hH1,map_mul,map_ofNat]
    rw [show rr.H=4*rr.Am1-1 by dsimp [rr]; rw [H_def],hAeval]
    linear_combination -he
  have hXcast : rr.X=ι X0 := by
    dsimp [rr,X0,X,q,b,ports]
    simp only [X_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have hbcast : rr.h=ι b0 := by
    dsimp [rr,b0,b,ports]
    simp only [h_def,ports,map_mul,map_natCast]
  have hdiv := Trace85Projection.graph_entire_product p v hb31 hl hh hv hz
  change rr.H∣(6*rr.h*rr.X)*(rr.X-ι T)*(ι T*rr.X+1) at hdiv
  have h6c : (6*ι b0*ι X0:DiffRing V)=ι (6*b0*X0) := by simp only [map_mul,map_ofNat]
  rw [hHcast,hXcast,hbcast,h6c] at hdiv
  exact Trace75ProductHeight.equality_of_height (6*b0*X0) X0 T H
    (mul_pos (mul_pos (by norm_num) hb0) hx) hproduct hdiv

#print axioms Trace85GraphPower.graph_power
end Trace85GraphPower
