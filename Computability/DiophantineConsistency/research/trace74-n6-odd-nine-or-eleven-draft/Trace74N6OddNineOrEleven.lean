import Trace74AtLeastFiveR7GraphExclusion
import Trace74GraphIndexUpper
import Trace74Pell
import DiophantineConsistency.ArithmeticPellCongruences

/-! UNCHECKED DRAFT. First index n=6 leaves main index r=9 or r=11. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6OddNineOrEleven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace74Pell Trace74GraphIndexUpper Trace74AtLeastFiveR7GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_six_odd_nine_or_eleven (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hqbig : (1073741824:V)≤q p v)
    (hcoord : 2*ycoord 6 (2*(firstParam p v-1)+1)=k v) :
    c p v=ycoord 9 (A p v-1) ∨ c p v=ycoord 11 (A p v-1) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<15) hb15
  obtain ⟨n,r,hn,hr,hodd,hnr,hr2n,hny,hc,hmod⟩ := graph_index_window p v hb15 hv hz
  have hy : ycoord n (2*(firstParam p v-1)+1)=ycoord 6 (2*(firstParam p v-1)+1) := by
    apply mul_left_cancel₀ (show (2:V)≠0 by norm_num)
    exact hny.trans hcoord.symm
  have hn6 : n=6 := (y_strictMono _).injective hy
  rw [hn6] at hnr hr2n
  have hr12 : r<12 := by simpa only [show (2:V)*6=12 by ring] using hr2n
  have hr7 : 7≤r := by
    simpa only [show (6:V)+1=7 by ring] using lt_iff_succ_le.mp hnr
  have hrne7 : r≠7 := by
    intro he
    have hh : c p v=ycoord 7 (A p v-1) := by simpa only [he] using hc
    exact graph_r7_impossible p v 6 hb hv hz hqbig (by norm_num) hcoord hh
  have hr8 : 8≤r := by
    have hh : (7:V)<r := lt_of_le_of_ne hr7 (Ne.symm hrne7)
    simpa only [show (7:V)+1=8 by ring] using lt_iff_succ_le.mp hh
  have hrne8 : r≠8 := by
    intro he
    rw [he,show (8:V)=2*4 by ring,mod_mul_self_right] at hodd
    exact zero_ne_one hodd
  have hr9 : 9≤r := by
    have hh : (8:V)<r := lt_of_le_of_ne hr8 (Ne.symm hrne8)
    simpa only [show (8:V)+1=9 by ring] using lt_iff_succ_le.mp hh
  by_cases he : r=9
  · left
    simpa only [he] using hc
  · right
    have hr10 : 10≤r := by
      have hh : (9:V)<r := lt_of_le_of_ne hr9 (Ne.symm he)
      simpa only [show (9:V)+1=10 by ring] using lt_iff_succ_le.mp hh
    have hrne10 : r≠10 := by
      intro h10
      rw [h10,show (10:V)=2*5 by ring,mod_mul_self_right] at hodd
      exact zero_ne_one hodd
    have hr11 : 11≤r := by
      have hh : (10:V)<r := lt_of_le_of_ne hr10 (Ne.symm hrne10)
      simpa only [show (10:V)+1=11 by ring] using lt_iff_succ_le.mp hh
    have hrle11 : r≤11 := by
      apply (add_le_add_iff_right (1:V)).mp
      simpa only [show (11:V)+1=12 by ring] using lt_iff_succ_le.mp hr12
    have heq : r=11 := le_antisymm hrle11 hr11
    simpa only [heq] using hc

#print axioms Trace74N6OddNineOrEleven.graph_first_six_odd_nine_or_eleven
end Trace74N6OddNineOrEleven
