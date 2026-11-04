import Trace74N2EtaModelWindow
import Trace74N2DiscreteGap
import Trace74FirstPellGap

/-! UNCHECKED DRAFT. Join the same-tuple model windows and first-Pell gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N2Exclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Pell Trace74FirstIndexGeometry Trace74FirstPellGap
open Trace74N2EtaModelWindow Trace74N2DiscreteGap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_small_k_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hq4 : 4≤q p v) (hsmall : k v=8*firstParam p v+4) : False := by
  have hleft := small_k_implies_X_lt_two_Y p v hb hv hz hsmall
  have hright := graph_small_k_right_window p v hb hv hz hq4 hsmall
  exact graph_XY_window_impossible p v hq4 hleft hright

theorem graph_first_pell_large (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hq4 : 4≤q p v) :
    32*(firstParam p v)^2+32*firstParam p v+6≤k v := by
  rcases graph_first_pell_gap p v hb hv hz with hsmall | hlarge
  · exact False.elim (graph_small_k_impossible p v hb hv hz hq4 hsmall)
  · exact hlarge

#print axioms Trace74N2Exclusion.graph_small_k_impossible
#print axioms Trace74N2Exclusion.graph_first_pell_large
end Trace74N2Exclusion
