import Trace74SignedRankAuxiliary
import Trace74Fold
import PellRankReduction

/-! UNCHECKED DRAFT. Guard-free main-index congruence for absolute signed rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74SignedRankMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace75Factors Trace74Representatives Trace74Fold Trace74SignedRankAuxiliary TenPositivePellRankReduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_rank_main (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ rp rn r : V, 3≤r ∧
      (regs (ports p) (masked p v)).rank=ι rp-ι rn ∧
      c p v=ycoord r (A p v-1) ∧ SignMod (c p v) (absdiff rp rn) r := by
  let rr := regs (ports p) (masked p v)
  obtain ⟨rp,rn,I,j,h,hI,hj,hdiv,hrank,hjx,hjy,htarget,hrmod⟩ := graph_signed_rank_auxiliary p v hb hv hz
  obtain ⟨r,j0,I0,hr,hrj,hodd,hj0,hI0,hc,hj0x,hj0y,hdiv0⟩ := graph_odd_ordinate p v hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk2 : 2≤k v := by
    simpa only [k,show (2:V)=1+1 by ring] using
      _root_.add_le_add (pos_iff_one_le.mp (hv 8)) (pos_iff_one_le.mp (hv 9))
  have hkY : k v≤k v*Y p v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v)
  have hc2 : 2<c p v := lt_of_le_of_lt (le_trans hk2 hkY) (by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ (hv 8))
  have hrne1 : r≠1 := by
    intro he
    rw [he] at hc
    have hy1 : ycoord 1 (A p v-1)=1 := by simpa using y_succ (0:V) (A p v-1)
    rw [hy1] at hc
    rw [hc] at hc2
    exact (not_lt_of_ge (by simp : (2:V)≥1)) hc2
  have h1r : 1<r := lt_of_le_of_ne (pos_iff_one_le.mp hr) (Ne.symm hrne1)
  have hr2 : 2≤r := by simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp h1r
  have hrne2 : r≠2 := by intro he; rw [he] at hodd; norm_num at hodd
  have h2r : 2<r := lt_of_le_of_ne hr2 (Ne.symm hrne2)
  have hr3 : 3≤r := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp h2r
  have hdiv' : c p v*c p v∣ycoord j (A p v-1) := by rwa [hjy]
  have htarget' : SignMod (xcoord j (A p v-1)) (c p v) (ycoord (2*h+1) (A p v-1)) := by rwa [hjx]
  have hmain := rank_to_main_index j (2*h+1) (A p v-1) (c p v) r (absdiff rp rn)
    hj hr3 hc hdiv' htarget' hrmod
  exact ⟨rp,rn,r,hr3,hrank,hc,hmain⟩

#print axioms Trace74SignedRankMain.graph_signed_rank_main
end Trace74SignedRankMain
