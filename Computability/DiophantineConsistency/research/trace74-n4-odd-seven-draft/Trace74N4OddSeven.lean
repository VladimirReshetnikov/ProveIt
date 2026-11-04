import Trace74N4R5GraphExclusion
import Trace74GraphIndexUpper
import DiophantineConsistency.ArithmeticPellCongruences

/-! UNCHECKED DRAFT. The r=5 exclusion leaves r=7 for first index n=4. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4OddSeven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace74Pell Trace74GraphIndexUpper Trace74N4R5GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_four_odd_seven (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord 4 (2*(firstParam p v-1)+1)=k v) :
    c p v=ycoord 7 (A p v-1) := by
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  obtain ⟨n,r,hn,hr,hodd,hnr,hr2n,hny,hc,hmod⟩ := graph_index_window p v hb15 hv hz
  have hy : ycoord n (2*(firstParam p v-1)+1)=ycoord 4 (2*(firstParam p v-1)+1) := by
    apply mul_left_cancel₀ (show (2:V)≠0 by norm_num)
    exact hny.trans hcoord.symm
  have hn4 : n=4 := (y_strictMono _).injective hy
  rw [hn4] at hnr hr2n
  have hr8 : r<8 := by simpa only [show (2:V)*4=8 by ring] using hr2n
  have hr5 : 5≤r := by
    simpa only [show (4:V)+1=5 by ring] using lt_iff_succ_le.mp hnr
  have hrne5 : r≠5 := by
    intro he
    have hh : c p v=ycoord 5 (A p v-1) := by simpa only [he] using hc
    exact graph_n4_r5_impossible p v hb31 hv hz hcoord hh
  have hr6 : 6≤r := by
    have hh : (5:V)<r := lt_of_le_of_ne hr5 (Ne.symm hrne5)
    simpa only [show (5:V)+1=6 by ring] using lt_iff_succ_le.mp hh
  have hrne6 : r≠6 := by
    intro he
    rw [he,show (6:V)=2*3 by ring,mod_mul_self_right] at hodd
    exact zero_ne_one hodd
  have hr7 : 7≤r := by
    have hh : (6:V)<r := lt_of_le_of_ne hr6 (Ne.symm hrne6)
    simpa only [show (6:V)+1=7 by ring] using lt_iff_succ_le.mp hh
  have hrle7 : r≤7 := by
    apply (add_le_add_iff_right (1:V)).mp
    simpa only [show (7:V)+1=8 by ring] using lt_iff_succ_le.mp hr8
  have heq : r=7 := le_antisymm hrle7 hr7
  simpa only [heq] using hc

#print axioms Trace74N4OddSeven.graph_first_four_odd_seven
end Trace74N4OddSeven
