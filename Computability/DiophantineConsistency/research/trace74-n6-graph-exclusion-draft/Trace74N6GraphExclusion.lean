import Trace74N6OddEleven
import Trace74N6R11TupleExclusion
import Trace74Pell

/-! UNCHECKED DRAFT. Exclude first index 6 for the same positive 74 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Pell
open Trace74N6OddEleven Trace74N6R11TupleExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_six_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hqbig : (1073741824:V)≤q p v)
    (hcoord : 2*ycoord 6 (2*(firstParam p v-1)+1)=k v) : False := by
  have hq260 : (260:V)≤q p v := le_trans (by norm_num) hqbig
  have hc := graph_first_six_odd_eleven p v hb15 hv hz hqbig hcoord
  exact tuple_n6_r11_impossible p v hv hq260 hcoord hc

#print axioms Trace74N6GraphExclusion.graph_first_six_impossible
end Trace74N6GraphExclusion
