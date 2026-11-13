import Trace74OddOrdinateBound

/-! UNCHECKED DRAFT. Consequence of the graph odd-ordinate lower bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74OddOrdinateKBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74OddOrdinateBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_k_lower (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    4*(Y p v*(X p v+1)+1)^2≤k v*(Y p v+1) := by
  have hη : v 8<k v := by
    change v 8<v 8+v 9
    exact lt_add_of_pos_right _ (hv 9)
  have hlt : c p v<k v*(Y p v+1) := by
    calc
      c p v=k v*Y p v+v 8 := rfl
      _<k v*Y p v+k v := add_lt_add_left hη _
      _=k v*(Y p v+1) := by ring
  have hle : c p v+1≤k v*(Y p v+1) := lt_iff_succ_le.mp hlt
  have hA : A p v=Y p v*(X p v+1) := by
    change X p v*Y p v+Y p v=Y p v*(X p v+1)
    ring
  have h := graph_ordinate_lower p v hb hv hz
  rw [hA] at h
  exact le_trans h hle

#print axioms Trace74OddOrdinateKBound.graph_k_lower
end Trace74OddOrdinateKBound
