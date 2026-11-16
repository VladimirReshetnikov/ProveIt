import PA194OccurrenceCore

/-! Extensionality of the exact occurrence core below its packed rank. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194OccurrenceLocality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OccurrenceCore

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- The next occurrence bit only consults earlier packed indices. -/
theorem core_local (x ih jh : V)
    (h : ∀ y < x, bitDef.val.Evalb ![y,ih] ↔ bitDef.val.Evalb ![y,jh]) :
    occurrenceCore.val.Evalb ![x,ih] ↔ occurrenceCore.val.Evalb ![x,jh] := by
  rw [occurrenceCore_eval, occurrenceCore_eval]
  unfold coreMeaning
  constructor <;> intro hx <;> obtain ⟨hn, hh⟩ := hx <;> refine ⟨hn, ?_⟩
  · rcases hh with h0 | h1 | h2
    · refine Or.inl ⟨h0.1, ?_⟩
      rcases h0.2 with h0 | h0
      · exact Or.inl ⟨h0.1, (h _ h0.1).mp h0.2⟩
      · exact Or.inr ⟨h0.1, (h _ h0.1).mp h0.2⟩
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨h2.1, ?_⟩)
      rcases h2.2 with hb | hb
      · exact Or.inl hb
      · exact Or.inr ⟨hb.1, (h _ hb.1).mp hb.2⟩
  · rcases hh with h0 | h1 | h2
    · refine Or.inl ⟨h0.1, ?_⟩
      rcases h0.2 with h0 | h0
      · exact Or.inl ⟨h0.1, (h _ h0.1).mpr h0.2⟩
      · exact Or.inr ⟨h0.1, (h _ h0.1).mpr h0.2⟩
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ⟨h2.1, ?_⟩)
      rcases h2.2 with hb | hb
      · exact Or.inl hb
      · exact Or.inr ⟨hb.1, (h _ hb.1).mpr hb.2⟩
#print axioms core_local
end PA194OccurrenceLocality
