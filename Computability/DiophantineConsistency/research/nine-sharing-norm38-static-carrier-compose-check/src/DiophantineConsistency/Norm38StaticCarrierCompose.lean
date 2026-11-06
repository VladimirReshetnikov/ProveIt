import DiophantineConsistency.Norm38ReferenceTerminals
import DiophantineConsistency.Norm38StaticCarrierConditional

/-! Candidate composition of checked terminal agreement and norm implication. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem static_gates_norms_imply_value (ports : Fin 4 → V) (w : Fin 38 → V)
    (hg : NormAssignment38.gatesHold ι ports w)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    Carrier65.value (fun j => ι (ports j))
      (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) = 0 :=
  static_terminals_norms_imply_value ports w (static_terminals_agree ports w hg) hn

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.static_gates_norms_imply_value
