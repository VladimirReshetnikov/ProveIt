import DiophantineConsistency.CompactWordDefinability
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactWordExistence
open DiophantineConsistency CompactMarkedTransport CompactCyclicBridge CompactWordDefinability
open DiophantineConsistency.ArithmeticWangPlane
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem supplied_word_equivalence (N s : V) :
    (∃ a : V → V, (𝚺₁-Function₁ a) ∧ MarkedWord a N s) ↔
    (∃ b : V → V, (𝚺₁-Function₁ b) ∧ RawCompactWord b N s) := by
  constructor
  · rintro ⟨a, ha, hw⟩
    letI : 𝚺₁-Function₁ a := ha
    have hf := forward_marked_word hw
    refine ⟨(fun j => CompactTableLookup.rowLookup (a j)), forward_composition a, ?_⟩
    exact ⟨hf.pos, hf.tile_lt, hf.marker, hf.east, hf.south⟩
  · rintro ⟨b, hb, hw⟩
    letI : 𝚺₁-Function₁ b := hb
    exact ⟨(fun j => CompactInverseDraft.inverseLookup (b j)), inverse_composition b,
      reverse_supplied_word hw⟩
#print axioms CompactWordExistence.supplied_word_equivalence
end CompactWordExistence
