module
import all M6PA.Scheduler.ActualCommandStepGraph
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCompilerHaltingWord
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualCommandWordGraph ActualCompilerHaltingWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every nonzero execution code is read through the same four HFS fields.
This concerns command-state decoding, not physical-file projection. -/
theorem step_state_normalize (atom state : V) (hs : state≠0) :
    stepValue atom state=stepValue atom (stateCode (nth state 0) (nth state 1) (nth state 2) (nth state 3)) := by
  unfold stepValue stepExpr shift mp ax
  expose_pa215_step_helpers
  have h1 (x xs : V) : nth (x∷xs) 1=nth xs 0 := by
    simpa only [zero_add] using nth_adjoin_succ x xs 0
  have h2 (x xs : V) : nth (x∷xs) 2=nth xs 1 := by
    simpa only [one_add_one_eq_two] using nth_adjoin_succ x xs 1
  have h3 (x xs : V) : nth (x∷xs) 3=nth xs 2 := by
    simpa only [two_add_one_eq_three] using nth_adjoin_succ x xs 2
  simp [ActualWordExpression.eval,ActualCheckExpression.eval,stateCode,hs,h1,h2,h3,eval_source_pair]

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem refutation_word_halts_any (code state : V)
    (hc : ActualCheckerBlueprint.verifyValue code=2) :
    wordValue (haltWord code) state=0 := by
  by_cases hs : state=0
  · simp [hs]
  · have he := refutation_word_halts code (nth state 0) (nth state 1) (nth state 2) (nth state 3) hc
    rw [haltWord,word_cons] at he ⊢
    rw [step_state_normalize _ state hs]
    exact he
end Peano
#print axioms step_state_normalize
#print axioms refutation_word_halts_any
end M6.PA.ActualCommandStepGraph

