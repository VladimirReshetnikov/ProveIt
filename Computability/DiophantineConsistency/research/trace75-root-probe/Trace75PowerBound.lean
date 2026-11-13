import Trace75IndexAlignment
import Direct80ScaledGrowthMinus

/-! Trace75 rank exponential bound via its unscaled Pell witnesses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75PowerBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence
open Trace75Factors Trace75Rank Trace75Pell Trace75RankExact Trace75IndexAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_power_bound (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    Exp.exp (rankNat p v)<Y p v := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hq16 : (16:V)≤q p v := by
    unfold q b
    calc
      (16:V)=15*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb15 hj (by simp) (by simp)) 1
  have hX : (16:V)≤X p v := calc
    (16:V)≤q p v := hq16
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (show (0:V)≤q p v by simp)
    _=X p v := rfl
  obtain ⟨n,_hn,_hnR,hrel,hny,hc⟩ := graph_first_main_alignment p v hb31 hl hh hv hz
  obtain ⟨_heval,hRlo,_hodd,_hc,_hwindow⟩ := graph_rank_exact p v hb31 hl hh hv hz
  have hR : (24:V)≤rankNat p v := le_trans (by norm_num : (24:V)≤3*16)
    (le_trans (mul_le_mul_of_nonneg_left hq16 (by simp)) (le_of_lt hRlo))
  have hn3 : 3≤n := by
    by_contra hn3
    have hnlt : n<3 := lt_of_not_ge hn3
    have hnplus : n+1≤2+1 := by
      simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hnlt
    have hnle : n≤2 := (add_le_add_iff_right (1:V)).mp hnplus
    have h2n : 2*n≤4 := by
      simpa only [show (2:V)*2=4 by ring] using mul_le_mul_of_nonneg_left hnle (show (0:V)≤2 by simp)
    have h25 : (25:V)≤rankNat p v+1 := by
      simpa only [add_comm,show (1:V)+24=25 by ring,show (24:V)+1=25 by ring] using add_le_add_right hR (1:V)
    have hbad : (25:V)≤4 := le_trans h25 (by rw [←hrel]; exact h2n)
    norm_num at hbad
  let r : V := n-1
  have hn1 : 1≤n := le_trans (by norm_num : (1:V)≤3) hn3
  have hrplus : r+1=n := tsub_add_cancel_of_le hn1
  have hr2 : 2≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrplus]
    simpa only [show (2:V)+1=3 by ring] using hn3
  have hmform : rankNat p v=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      rankNat p v+1=2*n := hrel.symm
      _=2*(r+1) := by rw [hrplus]
      _=(2*r+1)+1 := by ring
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hS : 1≤Y p v := pos_iff_one_le.mp hy
  have hkc : c p v=k v*Y p v+v 8 := rfl
  have hkez : k v=v 8+v 9 := rfl
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hc' : c p v=ycoord (2*r+1) (Y p v*(X p v+1)-1) := by
    simpa only [hmform,hA] using hc
  have hp : firstParam p v=X p v*Y p v*Y p v := by dsimp [firstParam]; ring
  have hk' : k v=2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1) := by
    rw [hrplus,←hp]
    exact hny.symm
  have hg := Direct80ScaledGrowthMinus.power_bound_scaled_minus (X p v) (Y p v)
    (Y p v) r (k v) (c p v) (v 8) (v 9) hX hS hr2 hkc hkez (hv 9) hc' hk'
  simpa only [hmform] using hg

#print axioms Trace75PowerBound.graph_power_bound
end Trace75PowerBound
