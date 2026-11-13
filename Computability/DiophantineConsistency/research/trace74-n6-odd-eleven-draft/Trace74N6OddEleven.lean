import Trace74N6OddNineOrEleven
import Trace74N6R9GraphExclusion
import Trace74Pell

/-! UNCHECKED DRAFT. First index 6 forces main index 11 for the same 74 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6OddEleven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74N6OddNineOrEleven Trace74N6R9GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_six_odd_eleven (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hqbig : (1073741824:V)≤q p v)
    (hcoord : 2*ycoord 6 (2*(firstParam p v-1)+1)=k v) :
    c p v=ycoord 11 (A p v-1) := by
  have hq32 : (32:V)≤q p v := le_trans (by norm_num) hqbig
  rcases graph_first_six_odd_nine_or_eleven p v hb15 hv hz hqbig hcoord with h9 | h11
  · exact (graph_n6_r9_impossible p v hv hq32 hcoord h9).elim
  · exact h11

#print axioms Trace74N6OddEleven.graph_first_six_odd_eleven
end Trace74N6OddEleven
