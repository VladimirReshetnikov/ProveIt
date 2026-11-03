import Trace75Transport
import Trace74GuardedIff

/-! Trace75 zeros correspond to trace74 zeros with the explicit new guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75To74
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Transport Trace74Guarded Trace74GuardedIff
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_iff_guarded (p : Fin 4 → ℕ) (hb : 0<(p 0:V)) :
    (∃v : Fin 10 → V, (∀j,0<v j) ∧
      value75 (ports p) (fun j => ι (v j)) = 0) ↔
    (∃v : Fin 10 → V, (∀j,0<v j) ∧ v 1+v 2<Trace74Guarded.q p v ∧
      Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    have hg : v 1+v 2<Trace74Guarded.q p v := by
      change v 1+v 2<Trace75Factors.q p v
      exact (graph_transport_and_mask p v hb hv hz).2
    exact ⟨flip p v,old_to_guarded p v hv hg hz⟩
  · rintro ⟨v,hv,hg,hz⟩
    exact ⟨flip p v,guarded_to_old p v hv hg hz⟩

#print axioms Trace75To74.positive_zero_iff_guarded
end Trace75To74
