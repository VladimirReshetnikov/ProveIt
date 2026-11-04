import Trace74N3GraphExclusion
import Trace74FirstIndexThree
import Trace74FirstIndexResidue

/-! UNCHECKED DRAFT. Every first-Pell index in the same 74 zero is at least 4. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FirstIndexFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74FirstIndexThree Trace74FirstIndexResidue Trace74N3GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_index_ge_four (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 4≤n := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hj1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hq4 : (4:V)≤q p v := by
    unfold q b
    calc
      (4:V)≤31*1+1 := by norm_num
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb31 hj1 (by simp) (by simp)) 1
  have hn3 := graph_first_index_ge_three p v n hb hv hz hq4 hcoord
  have hne : n≠3 := by
    intro hn
    have hh : 2*ycoord 3 (2*(firstParam p v-1)+1)=k v := by simpa only [hn] using hcoord
    exact graph_first_three_impossible p v hb31 hv hz hh
  have hn : (3:V)<n := lt_of_le_of_ne hn3 (Ne.symm hne)
  simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp hn

theorem graph_exists_first_index_ge_four (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n : V, 4≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨n,hn,hcoord,hres⟩ := graph_first_index_residue p v hb hv hz
  exact ⟨n,graph_first_index_ge_four p v n hb31 hv hz hcoord,hcoord,hres⟩

#print axioms Trace74FirstIndexFour.graph_first_index_ge_four
#print axioms Trace74FirstIndexFour.graph_exists_first_index_ge_four
end Trace74FirstIndexFour
