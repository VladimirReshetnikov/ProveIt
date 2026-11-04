import Trace74N5GraphExclusion
import Trace74FirstIndexFive
import Trace74FirstIndexResidue
import Trace74Pell

/-! UNCHECKED DRAFT. The same 74 zero has first Pell index at least 6
under the explicit q≥2³⁰ condition. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FirstIndexSix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74FirstIndexFive Trace74FirstIndexResidue Trace74N5GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_index_ge_six (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hqbig : (1073741824:V)≤q p v)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 6≤n := by
  have hn5 := graph_first_index_ge_five p v n hb31 hv hz hcoord
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  have hne : n≠5 := by
    intro hn
    have hh : 2*ycoord 5 (2*(firstParam p v-1)+1)=k v := by simpa only [hn] using hcoord
    exact graph_first_five_impossible p v hb15 hv hz hqbig hh
  have hn : (5:V)<n := lt_of_le_of_ne hn5 (Ne.symm hne)
  simpa only [show (5:V)+1=6 by ring] using lt_iff_succ_le.mp hn

theorem graph_exists_first_index_ge_six (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hqbig : (1073741824:V)≤q p v) :
    ∃ n : V, 6≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨n,hn,hcoord,hres⟩ := graph_first_index_residue p v hb hv hz
  exact ⟨n,graph_first_index_ge_six p v n hb31 hv hz hqbig hcoord,hcoord,hres⟩

#print axioms Trace74FirstIndexSix.graph_first_index_ge_six
#print axioms Trace74FirstIndexSix.graph_exists_first_index_ge_six
end Trace74FirstIndexSix
