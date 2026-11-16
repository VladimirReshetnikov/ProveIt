import PA194ValueBody
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance valBody_definable : 𝚺₁-Function₁ (valBody : V → V) := by
  haveI : 𝚺₁-Function₂ (translate : V → V → V) := translate_defined.to_definable
  haveI : 𝚺₁-Function₁ (childParameters : V → V) := childParameters_defined.to_definable
  show 𝚺₁-Function₁ (fun s : V => translate (childParameters (idParam (s+1))) s)
  definability

theorem valBody_has_domain (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    ∃ r : V, valBody s = domainCode (^#(0 : V)) ^⋏ r ∧ IsSemiformula SourceL 1 r := by
  let P : V → Prop := fun s => ∃ r : V, valBody s = domainCode (^#(0 : V)) ^⋏ r
  have hP : 𝚺₁-Predicate P := by dsimp [P]; definability
  have hall : ∀ s : V, IsSemiterm PA194PAeq.language 0 s → P s := by
    apply term_induction hP
    · intro i
      exact ⟨_, by rw [valBody_fvar]; rfl⟩
    · exact ⟨_, by rw [valBody_zero]; rfl⟩
    · intro a ha _
      exact ⟨_, by rw [valBody_succ ha]; rfl⟩
    · intro a b ha hb _ _
      exact ⟨_, by rw [valBody_add ha hb]; rfl⟩
    · intro a b ha hb _ _
      exact ⟨_, by rw [valBody_mul ha hb]; rfl⟩
  obtain ⟨r,hr⟩ := hall s hs
  have hv := valBody_valid hs
  rw [hr] at hv
  exact ⟨r,hr,(IsSemiformula.and.mp hv).2⟩
#print axioms valBody_definable
#print axioms valBody_has_domain
end generic
end PA194GuardedCompiler
