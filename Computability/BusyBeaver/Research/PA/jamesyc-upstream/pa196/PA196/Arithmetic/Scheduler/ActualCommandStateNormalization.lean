module
import PA196.Arithmetic.CommandStep
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.CompilerHaltingWord
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.CommandStep
open M6 M6.PA PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open CommandWord CompilerHaltingWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every nonzero execution code is read through the same four HFS fields.
This concerns command-state decoding, not physical-file projection. -/
theorem step_state_normalize (atom state : V) (hs : state≠0) :
    stepValue atom state=stepValue atom (stateCode (nth state 0) (nth state 1) (nth state 2) (nth state 3)) := by
  unfold stepValue stepExpr shift mp ax
  simp only [CommandStep.zero,CommandStep.top,CommandStep.stack,CommandStep.cacheD,
    CommandStep.cacheH,CommandStep.tag,CommandStep.fields,CommandStep.first,CommandStep.second,
    CommandStep.state,CommandStep.pair,CommandStep.imp,CommandStep.headValue,CommandStep.push]
  have h1 (x xs : V) : nth (x∷xs) 1=nth xs 0 := by
    simpa only [zero_add] using nth_adjoin_succ x xs 0
  have h2 (x xs : V) : nth (x∷xs) 2=nth xs 1 := by
    simpa only [one_add_one_eq_two] using nth_adjoin_succ x xs 1
  have h3 (x xs : V) : nth (x∷xs) 3=nth xs 2 := by
    simpa only [two_add_one_eq_three] using nth_adjoin_succ x xs 2
  simp [WordExpression.eval,Scalar.eval,stateCode,hs,h1,h2,h3,eval_source_pair]

section Peano
variable [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
theorem refutation_word_halts_any (code state : V)
    (hc : Checker.verifyValue code=2) :
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
end PA196.Arithmetic.CommandStep

