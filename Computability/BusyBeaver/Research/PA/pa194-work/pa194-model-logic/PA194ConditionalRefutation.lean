import PA194ConditionalProofCompiler
import PA194RootFormula
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open ConPA.Sequent
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

theorem translatedSequent_empty (param : V) : translatedSequent param (∅ : V) = ∅ := by
  simp [translatedSequent,emptyset_def,setList_empty]
theorem translatedSequent_singleton (param p : V) :
    translatedSequent param ({p} : V) = {translateFormula param p} := by
  rw [singleton_eq_insert,translatedSequent_insert,translatedSequent_empty,← singleton_eq_insert]

theorem conditional_refutation {d : V} (hd : Proof U d (^⊥ : V))
    (S : RemainingRules U T (rootParameters d)) : ∃ e, Proof T e (^⊥ : V) := by
  obtain ⟨e,he⟩ := conditional_compile U T (rootParameters_valid d) S hd.2 (rootParameters_length d)
  refine ⟨e,?_⟩
  simpa [Proof,hd.1,translatedSequent_singleton,translate_falsum] using he
#print axioms translatedSequent_singleton
#print axioms conditional_refutation
end generic
end PA194FormulaDispatcher
