import Trace74N4GraphExclusion
import Trace74FirstIndexFour
import Trace74FirstIndexResidue

/-! UNCHECKED DRAFT. Every first-Pell index in the same 74 zero is at least 5. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FirstIndexFive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74FirstIndexFour Trace74FirstIndexResidue Trace74N4GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_index_ge_five (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 5≤n := by
  have hn4 := Trace74FirstIndexFour.graph_first_index_ge_four p v n hb31 hv hz hcoord
  have hne : n≠4 := by
    intro hn
    have hh : 2*ycoord 4 (2*(firstParam p v-1)+1)=k v := by simpa only [hn] using hcoord
    exact Trace74N4GraphExclusion.graph_first_four_impossible p v hb31 hv hz hh
  have hn : (4:V)<n := lt_of_le_of_ne hn4 (Ne.symm hne)
  simpa only [show (4:V)+1=5 by ring] using lt_iff_succ_le.mp hn

theorem graph_exists_first_index_ge_five (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n : V, 5≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨n,hn,hcoord,hres⟩ := graph_first_index_residue p v hb hv hz
  exact ⟨n,graph_first_index_ge_five p v n hb31 hv hz hcoord,hcoord,hres⟩

#print axioms Trace74FirstIndexFive.graph_first_index_ge_five
#print axioms Trace74FirstIndexFive.graph_exists_first_index_ge_five
end Trace74FirstIndexFive
