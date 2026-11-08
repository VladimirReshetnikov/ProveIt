import DiophantineConsistency.BFS943.Trace80VariableHeight
import DiophantineConsistency.BFS943.Trace75ProductPower
import DiophantineConsistency.BFS943.Trace75ProductHeight

/-! # Exact power recovery `X = 2^R` for the 80/258 circuit (chart q1)

`Trace75GraphPower.graph_power` at a positive zero of `value80`: the q1
height bound (`Trace80VariableHeight`) and whole-product projection
(`Trace80Projection`) with the chart-free `Trace75ProductPower` and
`Trace75ProductHeight`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace80GraphPower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace80
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticPow
open Trace80Factors Trace80NormRank Trace80VariableHeight

theorem graph_power (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value80 (ports p) (fun j => ι (v j)) = 0) :
    X p v=Exp.exp (rankNat p v) := by
  let rr := regs (ports p) (fun j => ι (v j))
  obtain ⟨hzn,hm,hq4⟩ := Trace80Projection.zero_norm_data p v hb31 hv hz
  let R : V := rankNat p v
  let X0 : V := X p v
  let b0 : V := b p v
  let H : V := Hnat p v
  let T : V := Exp.exp R
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hb0 : 0<b0 := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X0 := mul_pos hq (mul_pos hq (hv 5))
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hq32 : (32:V)≤q p v := by
    unfold q b
    calc
      (32:V)=31*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb31 hj (by simp) (by simp)) 1
  have hqX : q p v≤X0 :=
    le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (mul_pos hq (hv 5)))
  have hX32 : (32:V)≤X0 := le_trans hq32 hqX
  have hbX : b0≤X0 := le_trans (show b0≤q p v by dsimp [b0,q]; simp) hqX
  have hbXX : b0*X0≤X0*X0 := mul_le_mul_of_nonneg_right hbX (by simp)
  obtain ⟨r,_hrpos,hR,_hsmall,hheight⟩ := graph_variable_height p v hb31 hl hh hv hz
  change R=2*r+1 at hR
  change power X0 (r+1)<H at hheight
  have h41 : (41:V)≤R := le_trans (by norm_num : (41:V)≤3*32)
    (le_trans (mul_le_mul_of_nonneg_left hq32 (by simp)) (le_of_lt (graph_rank_exact p v _ hb31 hl hh hv hzn hm).2.1))
  have hr20 : (20:V)≤r := by
    have h2 : (2:V)*20≤2*r := (add_le_add_iff_right (1:V)).mp (by
      simpa only [show (2:V)*20+1=41 by ring,←hR] using h41)
    exact le_of_mul_le_mul_left h2 (by norm_num : (0:V)<2)
  have hproduct : (b0*X0)*(X0+T)*(T*X0+1)<H := calc
    (b0*X0)*(X0+T)*(T*X0+1)<power X0 (r+1) := by
      simpa only [T,hR] using Trace75ProductPower.whole_product_lt_power X0 (b0*X0) r hX32 hbXX hr20
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
  have hdiv := Trace80Projection.graph_entire_product p v hb31 hl hh hv hz
  change rr.H∣(rr.h*rr.X)*(rr.X-ι T)*(ι T*rr.X+1) at hdiv
  rw [hHcast,hXcast,hbcast,←map_mul] at hdiv
  exact Trace75ProductHeight.equality_of_height (b0*X0) X0 T H (mul_pos hb0 hx) hproduct hdiv

#print axioms Trace80GraphPower.graph_power
end Trace80GraphPower
