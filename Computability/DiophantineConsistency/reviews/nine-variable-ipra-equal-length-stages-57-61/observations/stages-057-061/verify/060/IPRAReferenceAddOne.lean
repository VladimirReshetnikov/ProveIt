import DiophantineConsistency.IPRAErasedRemainingObligations
import DiophantineConsistency.IPRAAddOneDirect

/-! Exploratory transfer of the existing finite defining-equation proof of
`x+1 = S x` to the equality-only reference theory. This does not use the
native induction-image premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceAddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAOrderErasureRew IPRAOrderErasureHilbert
open IPRAOrderErasureTheoryTransfer IPRAEqualityOnlyReference
open IPRAAddOneDirect IPRANativeTheory

local instance : IPRAEqualityOnlyReference.language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

theorem finite_axiom_shape (p : Propositionᵢ PRALanguage.language) (hp : p ∈ Γ) :
    ∃ σ : Sentenceᵢ PRALanguage.language, p = Rewriting.emb σ ∧
      (EqualityAxiomI σ ∨ DefiningEquationI σ) := by
  simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.composition _ _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.composition _ _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.composition _ _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.projection _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.projection _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.projection _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.projection _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.recursionBase _ _)⟩
  · exact ⟨_, rfl, Or.inr (DefiningEquationI.recursionStep _ _)⟩
  · exact ⟨_, rfl, Or.inl (EqualityAxiomI.substitution IPRAEqualityTransGG.matrix)⟩
  · exact ⟨_, rfl, Or.inl EqualityAxiomI.refl⟩
  · exact ⟨_, rfl, Or.inl (EqualityAxiomI.substitution (IPRAFunctionCongruenceOpen.funMatrix PRALanguage.addCore (0 : Fin 2)))⟩
  · exact ⟨_, rfl, Or.inl (EqualityAxiomI.substitution (IPRAFunctionCongruenceOpen.funMatrix PRALanguage.addCore (1 : Fin 2)))⟩
  · exact ⟨_, rfl, Or.inl (EqualityAxiomI.substitution (IPRAFunctionCongruenceOpen.funMatrix PRAFiniteFunctionCodes.Code.succ (0 : Fin 1)))⟩

theorem addOne_image : referenceTheory ⊢ erase addOneI := by
  have hall : (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⋀(Γ.map erase) := by
    apply conjProof
    intro y hy
    let hex := List.mem_map.mp hy
    let p := Classical.choose hex
    have hp := (Classical.choose_spec hex).1
    have heq := (Classical.choose_spec hex).2
    rw [← heq]
    let shaped := finite_axiom_shape p hp
    let σ := Classical.choose shaped
    have hσ := (Classical.choose_spec shaped).1
    have hax := (Classical.choose_spec shaped).2
    change (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! erase p
    rw [hσ]
    rw [erase_emb]
    have hr : referenceTheory ⊢ erase σ := by
      cases hax with
      | inl he => exact ⟨Axiomatized.prfAxm (IPRAErasedEqualityImages.equality_images he)⟩
      | inr hd => exact ⟨Axiomatized.prfAxm (IPRAErasedDefiningImages.defining_images hd)⟩
    exact Classical.choice hr
  have hclosed : Γ ⊢[𝗜𝗻𝘁¹]! Rewriting.emb addOneI := by
    have h := Classical.choice add_one_closed_context
    convert h using 1
    simp [addOneI, Rewriting.emb, IPRANativeInduction.stepTerm, PRATheory.applyCode, Semiformulaᵢ.rew_rel]
    funext i; cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      funext j; cases j using Fin.cases with
      | zero => rfl
      | succ j => cases j using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
        | succ j => exact Fin.elim0 j
    | succ i => cases i using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]
      | succ i => exact Fin.elim0 i
  have hlogic := eraseHilbert (Entailment.FiniteContext.toDef hclosed)
  have hlogic' : (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language) ⊢!
      (⋀(Γ.map erase) 🡒 Rewriting.emb (erase addOneI)) := by
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (erase (⋀Γ 🡒 Rewriting.emb addOneI)) at hlogic
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (Semiformulaᵢ.imp (⋀(Γ.map erase)) (Rewriting.emb (erase addOneI)))
    simpa only [erase, erase_conj, erase_emb] using hlogic
  exact ⟨Entailment.Context.mdp (Entailment.Context.of hlogic') hall⟩

end DiophantineConsistency.IPRAReferenceAddOne
