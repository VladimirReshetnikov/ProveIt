import PellVariableGrowth
import Trace75IndexAlignment

/-! Variable-base Pell height bound for the actual 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75VariableHeight
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace75Rank Trace75Pell Trace75RankExact Trace75IndexAlignment TenPositivePellVariableGrowth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Hnat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := 4*A p v-1

theorem coefficient_gap (X S : V) (hX : 1≤X) (hS : 1≤S) :
    X*(2*(2*X*S*S+1)) < (2*(S*(X+1))+1)*(2*(S*(X+1))+1) := by
  apply ι_lt_ι.mp
  simp only [map_mul,map_add,map_one,map_ofNat]
  have hXR : (1:DiffRing V)≤ι X := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hX
  have hSR : (1:DiffRing V)≤ι S := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hS
  have hS2 : (0:DiffRing V)≤ι S*ι S := mul_self_nonneg _
  have hS2X : (0:DiffRing V)≤ι S*ι S*ι X := mul_nonneg hS2 (by linarith)
  have hSX : (ι X:DiffRing V)≤ι S*ι X := by nlinarith
  nlinarith

theorem graph_variable_height (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ r : V, 0<r ∧ rankNat p v=2*r+1 ∧ power (X p v) r<2*(Y p v+1) ∧
      power (X p v) (r+1)<Hnat p v := by
  obtain ⟨n,hn,_hnR,heq,hny,hc⟩ := graph_first_main_alignment p v hb31 hl hh hv hz
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hq16 : (16:V)≤q p v := by
    unfold q b
    calc
      (16:V)=15*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb15 hj (by simp) (by simp)) 1
  have hRlo : (24:V)≤rankNat p v := le_trans (by norm_num : (24:V)≤3*16)
    (le_trans (mul_le_mul_of_nonneg_left hq16 (by simp)) (le_of_lt (graph_rank_exact p v hb31 hl hh hv hz).2.1))
  have hn3 : 3≤n := by
    have h6 : (2:V)*3≤2*n := by
      rw [heq]
      have h := le_trans hRlo (show rankNat p v≤rankNat p v+1 by simp)
      exact le_trans (by norm_num) h
    exact le_of_mul_le_mul_left h6 (by norm_num : (0:V)<2)
  let r : V := n-1
  have hrplus : r+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hrpos : 0<r := tsub_pos_iff_lt.mpr (lt_of_lt_of_le (by norm_num : (1:V)<3) hn3)
  have hR : rankNat p v=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      rankNat p v+1=2*n := heq.symm
      _=2*(r+1) := by rw [hrplus]
      _=(2*r+1)+1 := by ring
  let S : V := Y p v
  let P : V := firstParam p v
  let a : V := A p v-1
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hS : 1≤S := pos_iff_one_le.mp hY
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hB : B+2=2*X p v*S*S+1 := calc
    B+2=2*(P-1+1)+1 := by dsimp [B]; ring
    _=2*P+1 := by rw [hP1]
    _=2*X p v*S*S+1 := by dsimp [P,firstParam,S]; ring
  have ha : 2*a+3=2*(S*(X p v+1))+1 := calc
    2*a+3=2*(a+1)+1 := by ring
    _=2*A p v+1 := by rw [hA1]
    _=2*(S*(X p v+1))+1 := by dsimp [A,S]; ring
  have hsep : X p v*(2*(B+2))<(2*a+3)*(2*a+3) := by
    rw [hB,ha]
    exact coefficient_gap (X p v) S hX1 hS
  have hlow := paired_comparison_strict (X p v) a B hsep r hrpos
  change 2*ycoord n B=k v at hny
  rw [←hrplus] at hny
  change c p v=ycoord (rankNat p v) a at hc
  rw [hR] at hc
  have hkpos : 0<k v := add_pos (hv 8) (hv 9)
  have hint : c p v<k v*(Y p v+1) := by
    change k v*Y p v+v 8<k v*(Y p v+1)
    have he : v 8<k v := lt_add_of_pos_right _ (hv 9)
    have hs := add_lt_add_of_le_of_lt (le_refl (k v*Y p v)) he
    simpa only [mul_add,mul_one] using hs
  have hcompare : power (X p v) r*k v<k v*(2*(Y p v+1)) := calc
    power (X p v) r*k v=2*(power (X p v) r*ycoord (r+1) B) := by rw [←hny]; ring
    _<2*ycoord (2*r+1) a := mul_lt_mul_of_pos_left hlow (by simp)
    _=2*c p v := by rw [hc]
    _<2*(k v*(Y p v+1)) := mul_lt_mul_of_pos_left hint (by simp)
    _=k v*(2*(Y p v+1)) := by ring
  have hpow : power (X p v) r<2*(Y p v+1) :=
    (mul_lt_mul_iff_of_pos_left hkpos).mp (by simpa only [mul_comm] using hcompare)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hSY : Y p v≤S := le_refl _
  have h4A : 1≤4*A p v := le_trans (pos_iff_one_le.mp hA) (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:V)≤4) (by simp : (0:V)≤A p v))
  have hH1 : Hnat p v+1=4*A p v := tsub_add_cancel_of_le h4A
  have hlarge : X p v*(2*(Y p v+1))+1≤Hnat p v+1 := by
    rw [hH1]
    have hAeq : A p v=S*(X p v+1) := by dsimp [A,S]; ring
    rw [hAeq]
    apply ι_le_ι.mp
    simp only [map_mul,map_add,map_one,map_ofNat]
    have hYr : (1:DiffRing V)≤ι (Y p v) := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hY1
    have hXr : (1:DiffRing V)≤ι (X p v) := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hX1
    have hSYr : (ι (Y p v):DiffRing V)≤ι S := ι_le_ι.mpr hSY
    have h1 := mul_nonneg (sub_nonneg.mpr hSYr) (show (0:DiffRing V)≤ι (X p v)+1 by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hYr) (show (0:DiffRing V)≤ι (X p v) by linarith)
    nlinarith
  have hheight : power (X p v) (r+1)<Hnat p v := by
    apply (add_lt_add_iff_right (1:V)).mp
    calc
      power (X p v) (r+1)+1=X p v*power (X p v) r+1 := by rw [power_succ]
      _<X p v*(2*(Y p v+1))+1 := by simpa only [add_comm] using _root_.add_lt_add_right (mul_lt_mul_of_pos_left hpow hX) (1:V)
      _≤Hnat p v+1 := hlarge
  exact ⟨r,hrpos,hR,hpow,hheight⟩

#print axioms Trace75VariableHeight.graph_variable_height
end Trace75VariableHeight
