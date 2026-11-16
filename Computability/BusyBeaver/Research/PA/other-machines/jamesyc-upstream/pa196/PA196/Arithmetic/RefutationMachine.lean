module
public import Mathlib.Tactic.FinCases
public import PA196.Arithmetic.Scheduler.SourceEnumerationFromTwo
public import PA196.Arithmetic.Machine.StartupLiteralTransport
public import PA196.Arithmetic.RefutationGraph
public import PA196.Arithmetic.Truth
@[expose] public section

namespace PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Machine.PA.InternalTrace Machine.PA.InternalTrace.CodedSource
open Machine.PA.InternalTrace.FixedTrace

attribute [local irreducible] Machine.Exact.PA.HaltingFormula.traceSentence
  CodedSource.Trace CodedSource.traceGraph

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* M6.PA.theory]

/-- A model-valued PA196 checker refutation drives the actual candidate-two
startup to the literal196-state machine's halt. All source and tape traces
are internal to the same model. -/
theorem refutation_implies_literal (code : V) (hc : Checker.verifyValue code=2) :
    V ⊧/![] haltingSentence := by
  let xs : V := fixedFile startupRegisters
  have hv : ValidStore xs := by simp [xs,ValidStore,fixedFile_length,startupRegisters]
  have hz (r : Fin 9) : registers xs r=if r.val=0 then 2 else 0 := by
    simp only [xs,registers,fixedFile_nth]
    fin_cases r <;> simp [startupRegisters]
  have hclean : CommandClean xs := by simp [CommandClean,hz]
  obtain ⟨n,cs,b,ht,hb⟩ := refutation_root_two_halts code xs hv hclean
    (by simpa using hz 0) (by simpa using hz 8) hc
  have ht' : Trace n cs (entryState (V := V)) b := by
    simpa only [entryState,xs] using ht
  exact source_halt_literal (V := V) (n := n) (cs := cs) (b := b) ht' hb

noncomputable def refutationHaltingSentence : ArithmeticSentence :=
  “∀ code, !RefutationGraph.formula code → !haltingSentence”

theorem pa_proves_refutation_halting : M6.PA.theory ⊢ refutationHaltingSentence := by
  apply Arithmetic.complete.{0} M6.PA.theory _
  intro V _ _
  simp only [refutationHaltingSentence,models_iff]
  simp [RefutationGraph.formula_graph]
  exact refutation_implies_literal

#print axioms refutation_implies_literal
#print axioms pa_proves_refutation_halting
end PA196.Arithmetic
