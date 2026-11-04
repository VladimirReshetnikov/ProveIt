import Trace74AtLeastSevenR9GraphExclusion
import Trace74GraphIndexUpper
import Trace74Pell
import DiophantineConsistency.ArithmeticPellCongruences

/-! UNCHECKED DRAFT. Same-witness first index n≥7 forces odd main r≥11. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74MainIndexEleven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace74Pell Trace74GraphIndexUpper Trace74AtLeastSevenR9GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_main_index_ge_eleven (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hq64 : (64:V)≤q p v) (hn7 : 7≤n)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) :
    ∃ r : V, 11≤r ∧ n<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<15) hb15
  obtain ⟨n',r,hn,hr,hodd,hnr,hr2n,hny,hc,hmod⟩ := graph_index_window p v hb15 hv hz
  have hy : ycoord n' (2*(firstParam p v-1)+1)=ycoord n (2*(firstParam p v-1)+1) := by
    apply mul_left_cancel₀ (show (2:V)≠0 by norm_num)
    exact hny.trans hcoord.symm
  have heq : n'=n := (y_strictMono _).injective hy
  rw [heq] at hnr hr2n
  have hr8 : 8≤r := by
    have hh : (7:V)<r := lt_of_le_of_lt hn7 hnr
    simpa only [show (7:V)+1=8 by ring] using lt_iff_succ_le.mp hh
  have hrne8 : r≠8 := by
    intro he
    rw [he,show (8:V)=2*4 by ring,mod_mul_self_right] at hodd
    exact zero_ne_one hodd
  have hr9 : 9≤r := by
    have hh : (8:V)<r := lt_of_le_of_ne hr8 (Ne.symm hrne8)
    simpa only [show (8:V)+1=9 by ring] using lt_iff_succ_le.mp hh
  have hrne9 : r≠9 := by
    intro he
    have hh : c p v=ycoord 9 (A p v-1) := by simpa only [he] using hc
    exact graph_r9_impossible p v n hb hv hz hq64 hn7 hcoord hh
  have hr10 : 10≤r := by
    have hh : (9:V)<r := lt_of_le_of_ne hr9 (Ne.symm hrne9)
    simpa only [show (9:V)+1=10 by ring] using lt_iff_succ_le.mp hh
  have hrne10 : r≠10 := by
    intro he
    rw [he,show (10:V)=2*5 by ring,mod_mul_self_right] at hodd
    exact zero_ne_one hodd
  have hr11 : 11≤r := by
    have hh : (10:V)<r := lt_of_le_of_ne hr10 (Ne.symm hrne10)
    simpa only [show (10:V)+1=11 by ring] using lt_iff_succ_le.mp hh
  exact ⟨r,hr11,hnr,hr2n,hodd,hc⟩

#print axioms Trace74MainIndexEleven.graph_main_index_ge_eleven
end Trace74MainIndexEleven
