import PA194PAeqInductionTheory
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem inductionTheory_mem_iff_typed (σ : Sentence PA194PAeq.language) :
    σ ∈ inductionTheory ↔ ∃ p : Semiproposition PA194PAeq.language 1,
      σ = (PA194PAeq.inductionFormula p).univCl := by
  change (ℕ ⊧/![(⌜σ⌝ : ℕ)] inductionUniform.val) ↔ _
  letI : 𝚫₁-Predicate (inductionPure : ℕ → Prop) via inductionUniform := inductionUniform_defined
  rw [HierarchySymbol.Defined.iff (φ := inductionUniform) (v := ![⌜σ⌝])]
  rw [inductionPure_iff]
  constructor
  · rintro ⟨code,hcode,heq⟩
    obtain ⟨p,hp⟩ := IsSemiformula.sound hcode
    rw [← hp,closedInduction_quote] at heq
    exact ⟨p,Sentence.quote_inj_iff.mp heq.symm⟩
  · rintro ⟨p,rfl⟩
    refine ⟨⌜p⌝,Semiformula.quote_isSemiformula p,?_⟩
    exact closedInduction_quote p
#print axioms inductionTheory_mem_iff_typed
end PA194PAeqBind
