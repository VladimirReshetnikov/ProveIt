import Trace74GraphIndexUpper
import DiophantineConsistency.ArithmeticPellCongruences

/-! UNCHECKED DRAFT. The 74 index window maps first index 3 to odd index 5. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N3OddFive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace74Pell Trace74GraphIndexUpper
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_three_odd_five (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord 3 (2*(firstParam p v-1)+1)=k v) :
    c p v=ycoord 5 (A p v-1) := by
  obtain ⟨n,r,hn,hr,hodd,hnr,hr2n,hny,hc,hmod⟩ := graph_index_window p v hb15 hv hz
  have hy : ycoord n (2*(firstParam p v-1)+1)=ycoord 3 (2*(firstParam p v-1)+1) := by
    apply mul_left_cancel₀ (show (2:V)≠0 by norm_num)
    exact hny.trans hcoord.symm
  have hn3 : n=3 := (y_strictMono _).injective hy
  rw [hn3] at hnr hr2n
  have hr6 : r<6 := by simpa only [show (2:V)*3=6 by ring] using hr2n
  have hr4 : 4≤r := by
    simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp hnr
  have hrne4 : r≠4 := by
    intro he
    rw [he,show (4:V)=2*2 by ring,mod_mul_self_right] at hodd
    exact zero_ne_one hodd
  have hr5 : 5≤r := by
    have hh : (4:V)<r := lt_of_le_of_ne hr4 (Ne.symm hrne4)
    simpa only [show (4:V)+1=5 by ring] using lt_iff_succ_le.mp hh
  have hrle5 : r≤5 := by
    apply (add_le_add_iff_right (1:V)).mp
    simpa only [show (5:V)+1=6 by ring] using lt_iff_succ_le.mp hr6
  have heq : r=5 := le_antisymm hrle5 hr5
  simpa only [heq] using hc

#print axioms Trace74N3OddFive.graph_first_three_odd_five
end Trace74N3OddFive
