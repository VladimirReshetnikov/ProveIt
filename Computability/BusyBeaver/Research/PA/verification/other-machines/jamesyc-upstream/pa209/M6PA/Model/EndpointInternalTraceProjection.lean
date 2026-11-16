module
/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
public import M6PA.Model.PATheory
public import M6PA.Model.PAInternalTrace
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace
open M6 M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] StepFormula.formula Step
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxRecDepth 2048 in
lemma prefix_halts {n qs ls rs l r : V} (h : Prefix n qs ls rs 215 l r) :
    V ⊧/![] HaltingFormula.traceSentence := by
  rcases h with ⟨_,_,_,hq0,hl0,hr0,hqn,_,_,hsteps⟩
  simp only [HaltingFormula.traceSentence, Semiformula.eval_ex, Semiformula.eval_ballLT, LogicalConnective.HomClass.map_and]
  refine ⟨n,qs,ls,rs,?_,?_,?_,?_,?_⟩
  · simpa [nth_defined.df] using hq0.symm
  · simpa [nth_defined.df] using hl0.symm
  · simpa [nth_defined.df] using hr0.symm
  · simpa [nth_defined.df, numeral_eq_natCast] using hqn.symm
  · intro i hi
    have hi' : i < n := by simpa using hi
    refine ⟨nth qs i,nth ls i,nth rs i,nth qs (i+1),nth ls (i+1),nth rs (i+1),?_,?_,?_,?_,?_,?_,?_⟩
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simp [nth_defined.df]
    · simpa [step_vector] using hsteps i hi'


def haltingProjectionSentence : ArithmeticSentence :=
  “∀ n qs ls rs l r, !prefixFormula n qs ls rs 215 l r → !HaltingFormula.traceSentence”

attribute [local irreducible] HaltingFormula.traceSentence

set_option maxRecDepth 2048 in
theorem pa_proves_halting_projection : theory ⊢ haltingProjectionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [haltingProjectionSentence,models_iff]
  simp [prefix_correct,numeral_eq_natCast]
  intro n qs ls rs l r h
  exact prefix_halts h

#print axioms prefix_halts
#print axioms pa_proves_halting_projection
end M6.Arithmetic.PA.InternalTrace

