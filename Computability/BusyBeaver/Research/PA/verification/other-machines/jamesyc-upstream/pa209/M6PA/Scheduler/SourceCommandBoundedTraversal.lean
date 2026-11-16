module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandResidualBounds
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualWordEncodingBlueprint ActualCommandWordGraph ActualCommandStepGraph
open ActualCompilerHaltingWord ActualCandidateBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem consume_add (n m initial : V) : consume (n+m) initial=consume m (consume n initial) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih => rw [← add_assoc,consume_succ,ih,consume_succ]

theorem consume_empty (n initial : V) : consume n (traversalState 0 initial)=traversalState 0 initial := by
  induction n using ISigma1.sigma1_succ_induction
  · unfold traversalState; definability
  case zero => simp
  case succ n ih =>
    rw [consume_succ,ih]
    simp [consumeStep,traversalState]

theorem consume_encoded_bound (xs initial n : V) (hn : len xs≤n) :
    consume n (traversalState (encodeValue xs) initial)=traversalState 0 (wordValue xs initial) := by
  rw [← add_tsub_self_of_le hn,consume_add,consume_encoded_word,consume_empty]

/-- Bounded execution of the candidate word; the bound itself may be nonstandard. -/
theorem candidate_consumption (code initial : V) :
    consume (candidateValue code+1) (traversalState (candidateValue code+1) initial)=
      traversalState 0 (wordValue (haltWord code) initial) := by
  rw [candidate_restore]
  exact consume_encoded_bound _ _ _ (encoded_length_le _)

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem refutation_candidate_consumption (code t w d h : V)
    (hc : ActualCheckerBlueprint.verifyValue code=2) :
    consume (candidateValue code+1)
      (traversalState (candidateValue code+1) (stateCode t w d h))=traversalState 0 0 := by
  rw [candidate_consumption,refutation_word_halts code t w d h hc]
end Peano
#print axioms consume_encoded_bound
#print axioms refutation_candidate_consumption
end M6.PA.SourceCommandEncodingInternal

