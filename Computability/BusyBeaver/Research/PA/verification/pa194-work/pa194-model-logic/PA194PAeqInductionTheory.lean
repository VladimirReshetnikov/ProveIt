import PA194PAeqStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
noncomputable def inductionTheory : Theory PA194PAeq.language :=
  {σ | ℕ ⊧/![(⌜σ⌝ : ℕ)] inductionUniform.val}
@[implicit_reducible] noncomputable def inductionTheoryDelta : inductionTheory.Δ₁ where
  ch := inductionUniform
  mem_iff := by
    intro φ
    constructor
    · intro h
      letI : 𝚫₁-Predicate (inductionPure : ℕ → Prop) via inductionUniform := inductionUniform_defined
      have hc : inductionPure (⌜φ⌝ : ℕ) := by
        exact (HierarchySymbol.Defined.iff (φ := inductionUniform) (v := ![⌜φ⌝])).mp h
      have hφ : shift PA194PAeq.language (⌜φ⌝ : ℕ) = ⌜φ⌝ := hc.1
      obtain ⟨σ,hσ⟩ := (standard_quote_shift_fixed_semisentence_iff 0 φ).mp hφ
      refine ⟨σ,?_,hσ.symm⟩
      simpa [inductionTheory,Sentence.quote_def,hσ] using h
    · rintro ⟨σ,hσ,rfl⟩
      simpa [inductionTheory,Sentence.quote_def] using hσ
  isDelta1 := inductionUniform_provablyProper
#print axioms inductionTheoryDelta
end PA194PAeqBind
