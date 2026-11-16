import PA194FullSepUniform
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The standard sentences recognized by the closed separation classifier. -/
noncomputable def fullSepTheory : Theory SourceL :=
  {σ | ℕ ⊧/![(⌜σ⌝ : ℕ)] fullSepUniform.val}

@[implicit_reducible] noncomputable def fullSepTheoryDelta : fullSepTheory.Δ₁ where
  ch := fullSepUniform
  mem_iff := by
    intro φ
    constructor
    · intro h
      letI : 𝚫₁-Predicate (fullSepPure : ℕ → Prop) via fullSepUniform := fullSepUniform_defined
      have hc : fullSepPure (⌜φ⌝ : ℕ) := by
        exact (HierarchySymbol.Defined.iff (φ := fullSepUniform) (v := ![⌜φ⌝])).mp h
      have hφ : shift SourceL (⌜φ⌝ : ℕ) = ⌜φ⌝ := hc.1
      obtain ⟨σ,hσ⟩ := (standard_quote_shift_fixed_semisentence_iff 0 φ).mp hφ
      refine ⟨σ, ?_, hσ.symm⟩
      simpa [fullSepTheory, Sentence.quote_def, hσ] using h
    · rintro ⟨σ,hσ,rfl⟩
      simpa [fullSepTheory, Sentence.quote_def] using hσ
  isDelta1 := fullSepUniform_provablyProper

#print axioms fullSepTheoryDelta
end PA194BindSource
