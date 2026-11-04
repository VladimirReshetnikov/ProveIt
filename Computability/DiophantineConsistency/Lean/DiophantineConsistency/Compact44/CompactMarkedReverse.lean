import DiophantineConsistency.Compact44.CompactMarkedTransport
import DiophantineConsistency.Compact44.CompactInverseInventory
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactMarkedReverse
open DiophantineConsistency CompactMarkedTransport CompactInverseDraft CompactRowTransport CompactTableLookup
open DiophantineConsistency.ArithmeticWangTable DiophantineConsistency.ArithmeticWangPlane
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inverse_zero : inverseLookup (0 : V) = 0 := by
  have h := inverse_forward (i := (0 : V)) (by simp)
  simpa only [row_zero] using h

theorem reverse_marked_word {b : V → V} {N s : V} (h : CompactWord b N s) :
    MarkedWord (fun j => inverseLookup (b j)) N s := by
  refine ⟨h.pos, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact (inverse_image (h.tile_lt j hj) (h.tile_ne j hj)).1
  · rw [h.marker]; exact inverse_zero
  · intro j hj j' hj' he
    have hi := inverse_image (h.tile_lt j hj) (h.tile_ne j hj)
    have hi' := inverse_image (h.tile_lt j' hj') (h.tile_ne j' hj')
    apply (horizontal_match_bounded hi.1 hi'.1).1
    simpa only [hi.2, hi'.2] using h.east j hj j' hj' he
  · intro j hj j' hj' he
    have hi := inverse_image (h.tile_lt j hj) (h.tile_ne j hj)
    have hi' := inverse_image (h.tile_lt j' hj') (h.tile_ne j' hj')
    apply (vertical_match_bounded hi.1 hi'.1).1
    simpa only [hi.2, hi'.2] using h.south j hj j' hj' he
#print axioms CompactMarkedReverse.reverse_marked_word
end CompactMarkedReverse
