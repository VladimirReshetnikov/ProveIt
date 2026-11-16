import PA194ClosedSepTheory
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The standard sentences recognized by the closed separation classifier. -/
noncomputable def closedSepTheory : Theory SourceL :=
  {σ | ℕ ⊧/![(⌜σ⌝ : ℕ)] closedSepUniform.val}

@[implicit_reducible] noncomputable def closedSepTheoryDelta : closedSepTheory.Δ₁ where
  ch := closedSepUniform
  mem_iff := by
    intro φ
    constructor
    · intro h
      letI : 𝚫₁-Predicate (closedSepPure : ℕ → Prop) via closedSepUniform := closedSepUniform_defined
      have hc : closedSepPure (⌜φ⌝ : ℕ) := by
        exact (HierarchySymbol.Defined.iff (φ := closedSepUniform) (v := ![⌜φ⌝])).mp h
      obtain ⟨p,_,hp,hshift,heq⟩ := hc
      have hφ : shift SourceL (⌜φ⌝ : ℕ) = ⌜φ⌝ := by
        rw [←heq]
        exact sepRootPure_shift_fixed p hp hshift
      obtain ⟨σ,hσ⟩ := (standard_quote_shift_fixed_semisentence_iff 0 φ).mp hφ
      refine ⟨σ, ?_, hσ.symm⟩
      simpa [closedSepTheory, Sentence.quote_def, hσ] using h
    · rintro ⟨σ,hσ,rfl⟩
      simpa [closedSepTheory, Sentence.quote_def] using hσ
  isDelta1 := closedSepUniform_provablyProper

#print axioms closedSepTheoryDelta
end PA194ModelLogic
