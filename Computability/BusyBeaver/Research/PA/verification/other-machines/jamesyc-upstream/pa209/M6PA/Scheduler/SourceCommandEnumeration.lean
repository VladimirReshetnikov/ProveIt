module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandBoundedTraversal
public import M6PA.Scheduler.ActualCommandStateNormalization
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCommandStepGraph ActualCommandWordGraph ActualCompilerHaltingWord ActualCandidateBlueprint

noncomputable def candidateRunGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “z n initial. ∃ packed result, !traversalStateGraph packed (n+1) initial ∧
    !consumeGraph result (n+1) packed ∧ !nthDef z result 1”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def candidateRun (n initial : V) : V := nth (consume (n+1) (traversalState (n+1) initial)) 1
theorem candidateRun_graph (z n initial : V) :
    candidateRunGraph.val.Evalb ![z,n,initial] ↔ z=candidateRun n initial := by
  simp [candidateRunGraph,traversalState_graph,consume_graph,candidateRun]

noncomputable def enumerationBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “z initial. z=initial”
  succ := candidateRunGraph.rew (Rew.subst ![#0,#2,#1])
noncomputable def enumerationConstruction : PR.Construction V enumerationBlueprint where
  zero := fun p => p 0
  succ := fun _ n state => candidateRun n state
  zero_defined := .mk fun v => by simp [enumerationBlueprint]
  succ_defined := .mk fun v => by simp [enumerationBlueprint,candidateRun_graph]
noncomputable def enumerationValue (n initial : V) : V := enumerationConstruction.result ![initial] n
noncomputable def enumerationGraph : 𝚺ᴬ₁.Semisentence 3 := enumerationBlueprint.resultDef
@[simp] theorem enumeration_zero (initial : V) : enumerationValue 0 initial=initial := by
  simp [enumerationValue,enumerationConstruction]
@[simp] theorem enumeration_succ (n initial : V) :
    enumerationValue (n+1) initial=candidateRun n (enumerationValue n initial) := by
  simp [enumerationValue,enumerationConstruction]
theorem enumeration_graph (z n initial : V) :
    enumerationGraph.val.Evalb ![z,n,initial] ↔ z=enumerationValue n initial := by
  simpa [enumerationGraph,enumerationValue,Matrix.constant_eq_singleton] using
    (enumerationConstruction (V:=V)).result_defined_iff ![z,n,initial]

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem refutation_candidate_run (code initial : V)
    (hc : ActualCheckerBlueprint.verifyValue code=2) : candidateRun (candidateValue code) initial=0 := by
  rw [candidateRun,candidate_consumption,refutation_word_halts_any code initial hc]
  have h1 (x xs : V) : nth (x∷xs) 1=nth xs 0 := by
    simpa only [zero_add] using nth_adjoin_succ x xs 0
  simp [traversalState,h1]

/-- Enumerating all earlier candidates cannot prevent the universal refuting
candidate from halting: its reset accepts every intermediate command state. -/
theorem refutation_enumeration_halts (code initial : V)
    (hc : ActualCheckerBlueprint.verifyValue code=2) :
    enumerationValue (candidateValue code+1) initial=0 := by
  rw [enumeration_succ,refutation_candidate_run code _ hc]
end Peano

noncomputable def enumerationHaltsSentence : ArithmeticSentence :=
  “∀ code, !ActualRefutationGraph.formula code → ∀ initial, ∃ candidate,
    !candidateGraph candidate code ∧ !enumerationGraph 0 (candidate+1) initial”
theorem pa_proves_refutation_enumeration_halts : theory ⊢ enumerationHaltsSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [enumerationHaltsSentence,models_iff,ActualRefutationGraph.formula_graph,
    candidate_graph,enumeration_graph,eq_comm]
  intro code hc initial
  simpa only [enumeration_succ] using (refutation_enumeration_halts code initial hc.symm).symm
#print axioms candidateRun_graph
#print axioms enumeration_graph
#print axioms refutation_enumeration_halts
#print axioms pa_proves_refutation_enumeration_halts
end M6.PA.SourceCommandEncodingInternal

