import PA194PAeqInductionEnvelope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def inductionPure (q : V) : Prop :=
  shift PA194PAeq.language q = q ∧ ∃ p < uncloseHistory q q, IsSemiformula PA194PAeq.language 1 p ∧ closedInduction p = q
noncomputable def inductionUniform : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “q. !(shiftGraph PA194PAeq.language) q q ∧ ∃ b, !uncloseHistoryGraph b q q ∧
    ∃ p < b, !(isSemiformula PA194PAeq.language).sigma 1 p ∧ !closedInductionGraph q p”)
  (.mkPi “q. !((shiftGraph PA194PAeq.language).graphDelta.pi) q q ∧ ∀ b, !uncloseHistoryGraph b q q →
    ∃ p < b, !(isSemiformula PA194PAeq.language).pi 1 p ∧ !(closedInductionGraph.graphDelta.pi) q p”)

theorem inductionUniform_defined : 𝚫₁-Predicate (inductionPure : V → Prop) via inductionUniform := by
  haveI : 𝚫₁-Function₁ (shift PA194PAeq.language : V → V) via (shiftGraph PA194PAeq.language).graphDelta :=
    HierarchySymbol.DefinedFunction.graph_delta (shift.defined (L := PA194PAeq.language))
  haveI : 𝚫₁-Function₁ (closedInduction : V → V) via closedInductionGraph.graphDelta :=
    HierarchySymbol.DefinedFunction.graph_delta closedInduction_defined
  refine ⟨?_⟩
  constructor
  · intro v
    simp [inductionUniform,HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_pi,HierarchySymbol.Defined.iff_delta_sigma]
  · intro v
    simp [inductionUniform,inductionPure,HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_sigma,eq_comm]

theorem inductionUniform_provablyProper : inductionUniform.ProvablyProperOn 𝗜𝚺₁ := by
  apply HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0}
  intro W _ _
  letI : 𝚫₁-Predicate (inductionPure : W → Prop) via inductionUniform := inductionUniform_defined
  exact HierarchySymbol.Defined.proper

theorem inductionPure_iff (q : V) : inductionPure q ↔ ∃ p, IsSemiformula PA194PAeq.language 1 p ∧ closedInduction p = q := by
  constructor
  · rintro ⟨_,p,_,hp,rfl⟩; exact ⟨p,hp,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(closedInduction_sentence hp).2,p,closedInduction_property_bound hp,hp,rfl⟩
#print axioms inductionUniform_defined
#print axioms inductionUniform_provablyProper
#print axioms inductionPure_iff
end generic
end PA194PAeqBind
