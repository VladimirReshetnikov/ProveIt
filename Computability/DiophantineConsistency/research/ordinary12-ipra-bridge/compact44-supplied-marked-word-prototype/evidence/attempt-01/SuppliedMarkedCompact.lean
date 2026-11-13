import DiophantineConsistency.CompactWordDefinability
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SuppliedMarkedCompact
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWangPlane
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem transport (a : V → V) [𝚺₁-Function₁ a] {N s : V} (h : MarkedWord a N s) :
    𝚺₁-Function₁ (fun j => CompactTableLookup.rowLookup (a j)) ∧
      CompactMarkedTransport.CompactWord (fun j => CompactTableLookup.rowLookup (a j)) N s :=
  ⟨CompactWordDefinability.forward_composition a,
    CompactMarkedTransport.forward_marked_word h⟩
#print axioms SuppliedMarkedCompact.transport
end SuppliedMarkedCompact
