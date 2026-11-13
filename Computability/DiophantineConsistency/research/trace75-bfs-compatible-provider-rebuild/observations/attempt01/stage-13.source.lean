import Trace75RankIndex
import Trace75MainIndex
import PellRankReduction

/-! Trace75 bounded natural rank equals the recovered odd main Pell index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75RankExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace75Factors Trace75Rank Trace75RankIndex Trace75MainIndex TenPositivePellRankReduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_rank_exact (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    (regs (ports p) (fun j => ι (v j))).rank=ι (rankNat p v) ∧
    3*q p v<rankNat p v ∧ rankNat p v%2=1 ∧
    c p v=ycoord (rankNat p v) (A p v-1) ∧
    rankNat p v+q p v^3+q p v+1≤q p v^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨hrank,hmask,hrlo,hrhi,hrC⟩ := graph_rank_window p v hb31 hl hh hv hz
  obtain ⟨r,j0,I0,hr3,hrj,hodd,hj0,hI0,hc,hrsize,hj0x,hj0y,hdiv0⟩ := graph_main_index p v hb hv hz
  obtain ⟨I,j,h,hI,hj,hdiv,hjx,hjy,htarget,hRmod⟩ := graph_rank_auxiliary p v hb31 hl hh hv hz
  have hdiv' : c p v*c p v∣ycoord j (A p v-1) := by rwa [hjy]
  have htarget' : SignMod (xcoord j (A p v-1)) (c p v) (ycoord (2*h+1) (A p v-1)) := by
    rwa [hjx]
  have hres := rank_to_main_index j (2*h+1) (A p v-1) (c p v) r (rankNat p v)
    hj hr3 hc hdiv' htarget' hRmod
  have hrpos : 0<r := lt_of_lt_of_le (by simp : (0:V)<3) hr3
  have hRpos : 0<rankNat p v := lt_of_le_of_lt (by simp) hrlo
  have heq : rankNat p v=r := sign_eq_of_half hRpos hrpos hrC hrsize hres
  refine ⟨hrank,hrlo,?_,?_,hrhi⟩
  · rwa [heq]
  · rwa [heq]

#print axioms Trace75RankExact.graph_rank_exact
end Trace75RankExact
