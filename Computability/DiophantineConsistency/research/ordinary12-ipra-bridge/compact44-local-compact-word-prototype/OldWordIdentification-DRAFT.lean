/- SOURCE-ONLY DRAFT: not compiled. Rebuild the old imports coherently first. -/
import DiophantineConsistency.CompactLocalWord
import DiophantineConsistency.CompactWordDefinability
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace OldWordIdentificationDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWangTable CompactMarkedTransport CompactMarkedReverse CompactWordDefinability
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem tab_eq (l : List ℕ) (k : ℕ) (i : V) :
    CompactLocalWord.tabValue l k i=ArithmeticWangTable.tabValue l k i := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [CompactLocalWord.tabValue,ArithmeticWangTable.tabValue]
    split <;> simp_all

theorem field_eq (f : CompactLocalWord.Quad → ℕ) (i : V) :
    CompactLocalWord.field f i=CompactRowTransport.compactField f i := by
  unfold CompactLocalWord.field CompactRowTransport.compactField
  exact tab_eq _ _ _

theorem local_to_old {b : V → V} {N s : V} (h : CompactLocalWord.Word b N s) :
    CompactMarkedTransport.CompactWord b N s := by
  refine ⟨h.pos,h.tile_lt,h.tile_ne,h.marker,?_,?_⟩
  · intro j hj j' hj' he
    rw [←field_eq,←field_eq]
    exact h.east j hj j' hj' he
  · intro j hj j' hj' he
    rw [←field_eq,←field_eq]
    exact h.south j hj j' hj' he

theorem local_to_marked {b : V → V} [𝚺₁-Function₁ b] {N s : V} (h : CompactLocalWord.Word b N s) :
    (𝚺₁-Function₁ (fun j => CompactInverseDraft.inverseLookup (b j))) ∧
      ArithmeticWangPlane.MarkedWord (fun j => CompactInverseDraft.inverseLookup (b j)) N s := by
  exact ⟨CompactWordDefinability.inverse_composition b, CompactMarkedReverse.reverse_marked_word (local_to_old h)⟩
end OldWordIdentificationDraft
