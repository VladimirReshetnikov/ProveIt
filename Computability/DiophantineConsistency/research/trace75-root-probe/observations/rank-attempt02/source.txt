import Trace75Transport
import Trace75Size
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Natural trace75 rank and its bounded-port window. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75Rank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticAdaptiveRankWindow2011
open Trace75Factors Trace75Transport Trace75Size
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rankNat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  (b p v*(q p v-v 1)+v 2)*(q p v*q p v-1)+((p 2:V)+q p v*(p 3:V))*v 0

theorem rank_eval_of_mask (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hq : 0<q p v) (hmask : v 1+v 2<q p v) :
    (regs (ports p) (fun j => ι (v j))).rank=ι (rankNat p v) := by
  have hqF : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hqq : 1≤q p v*q p v := pos_iff_one_le.mp (mul_pos hq hq)
  have hd1 : (ι (q p v-v 1):DiffRing V)=ι (q p v)-ι (v 1) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hqF]
  have hd2 : (ι (q p v*q p v-1):DiffRing V)=ι (q p v)*ι (q p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,tsub_add_cancel_of_le hqq,map_mul]
  simp only [rankNat,map_add,map_mul,hd1,hd2,map_natCast]
  simp only [rank_def,q_def,h_def,ports,b,q,map_mul,map_add,map_one,map_natCast]

theorem graph_rank_window (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    (regs (ports p) (fun j => ι (v j))).rank=ι (rankNat p v) ∧
      v 1+v 2<q p v ∧ 3*q p v<rankNat p v ∧
      rankNat p v+q p v^3+q p v+1≤q p v^4 ∧ 2*rankNat p v<c p v := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hm := (graph_transport_and_mask p v hb hv hz).2
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have he := rank_eval_of_mask p v hq hm
  have hwin := scalar_rank_window (q p v) (p 0:V) (p 2:V) (p 3:V) (v 0) (v 1) (v 2)
    hb (hv 0) (hv 1) (hv 2) hl hh rfl hm
  have hbq : q p v-1=b p v := by dsimp [q]; simp
  have hR : ((q p v-1)*(q p v-v 1)+v 2)*(q p v^2-1)+
      ((p 2:V)+q p v*(p 3:V))*v 0=rankNat p v := by
    rw [hbq]
    dsimp [rankNat]
    ring_nf
  rw [hR] at hwin
  have hJ1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hb31' : (31:V)≤b p v := le_trans hb31 (by
    change (p 0:V)≤(p 0:V)*v 0
    exact le_mul_of_one_le_right (by simp) hJ1)
  have hq32 : (32:V)≤q p v := by
    simpa only [q,show (32:V)=31+1 by ring,add_comm] using _root_.add_le_add_right hb31' (1:V)
  have hq4 : (4:V)≤q p v := le_trans (by norm_num) hq32
  have hq2 : (2:V)≤q p v := le_trans (by norm_num) hq32
  have hq1 : (1:V)≤q p v := le_trans (by norm_num) hq32
  have hG : 1≤b p v*(q p v-v 1)+v 2 := pos_iff_one_le.mp
    (add_pos_of_nonneg_of_pos (by simp) (hv 2))
  have hRlower : q p v*q p v-1≤rankNat p v := calc
    q p v*q p v-1≤(b p v*(q p v-v 1)+v 2)*(q p v*q p v-1) :=
      le_mul_of_one_le_left (by simp) hG
    _≤rankNat p v := by dsimp [rankNat]; simp
  have hsq : 4*q p v≤q p v*q p v := mul_le_mul_of_nonneg_right hq4 (by simp)
  have hsq1 : 1≤q p v*q p v := one_le_mul hq1 hq1
  have hsmall : 3*q p v+2≤q p v*q p v := calc
    3*q p v+2≤3*q p v+q p v := _root_.add_le_add_right hq2 _
    _=4*q p v := by ring
    _≤q p v*q p v := hsq
  have hsmall' : 3*q p v+1≤q p v*q p v-1 :=
    (le_tsub_iff_right hsq1).mpr (calc
      3*q p v+1+1=3*q p v+2 := by ring
      _≤q p v*q p v := hsmall)
  have hrlo : 3*q p v<rankNat p v := lt_of_lt_of_le (lt_add_one (3*q p v)) (le_trans hsmall' hRlower)
  have hwin' : rankNat p v+(q p v^3+q p v+1)≤q p v^4 := by
    simpa only [add_assoc] using hwin.2
  have hrhi : rankNat p v<q p v^4 := lt_of_lt_of_le (lt_add_of_pos_right _
    (show 0<q p v^3+q p v+1 by simp)) hwin'
  have hc := (graph_rank_size p v hb hv hz).2
  have hrC : 2*rankNat p v<c p v := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_of_lt hrhi) (by simp)) hc
  exact ⟨he,hm,hrlo,hwin.2,hrC⟩

#print axioms Trace75Rank.graph_rank_window
end Trace75Rank
