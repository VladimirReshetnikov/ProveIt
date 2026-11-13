import DiophantineConsistency.Compact44.CompactCyclicBridge
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactWordDefinability
open CompactTableLookup CompactInverseDraft CompactCyclicBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance row_lookup_sigma1 : 𝚺₁-Function₁[V] rowLookup := rowLookup_defined.of_zero
local instance inverse_lookup_sigma1 : 𝚺₁-Function₁[V] inverseLookup := inverseLookup_defined.of_zero

theorem forward_composition (a : V → V) [𝚺₁-Function₁ a] :
    𝚺₁-Function₁ (fun j => rowLookup (a j)) := by
  definability

theorem inverse_composition (b : V → V) [𝚺₁-Function₁ b] :
    𝚺₁-Function₁ (fun j => inverseLookup (b j)) := by
  definability
#print axioms CompactWordDefinability.forward_composition
#print axioms CompactWordDefinability.inverse_composition
end CompactWordDefinability
