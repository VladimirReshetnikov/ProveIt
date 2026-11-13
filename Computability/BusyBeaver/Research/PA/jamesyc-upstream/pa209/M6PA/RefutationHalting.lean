module
public import Mathlib.Tactic.FinCases
public import M6PA.Scheduler.SourceEnumerationFromTwo
public import M6PA.Model.StartupSourceTransport
public import M6PA.Model.EndpointInternalTraceProjection
@[expose] public section
namespace M6.Arithmetic.PA.InternalActualRefutation
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open InternalTrace InternalTrace.CodedSource InternalTrace.FixedTrace
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- This source compiler runs from the actual candidate2, zero-register entry.
It does not assume a source halt, a runtime oracle, or PA's consistency. -/
theorem refutation_implies_blank (code : V)
    (hc : M6.PA.ActualCheckerBlueprint.verifyValue code=2) :
    V ⊧/![] HaltingFormula.traceSentence := by
  let xs : V := fixedFile startupRegisters
  have hv : ValidStore xs := by simp [xs,ValidStore,fixedFile_length,startupRegisters]
  have hz (r : Fin 9) : registers xs r=if r.val=0 then 2 else 0 := by
    simp only [xs,registers,fixedFile_nth]
    fin_cases r <;> simp [startupRegisters]
  have hclean : CommandClean xs := by simp [CommandClean,hz]
  obtain ⟨n,cs,b,ht,hb⟩ := refutation_root_two_halts code xs hv hclean
    (by simpa using hz 0) (by simpa using hz 8) hc
  obtain ⟨k,qs,ls,rs,lf,rf,_,hs⟩ := source_halt_blank ht hb
  exact prefix_halts (show Prefix k qs ls rs 215 lf rf from hs)

noncomputable def refutationHaltingSentence : ArithmeticSentence :=
  “∀ code, !M6.PA.ActualRefutationGraph.formula code → !HaltingFormula.traceSentence”
noncomputable def noActualRefutationSentence : ArithmeticSentence :=
  “∀ code, ¬!M6.PA.ActualRefutationGraph.formula code”

theorem pa_proves_refutation_halting : theory ⊢ refutationHaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [refutationHaltingSentence,models_iff]
  simp [M6.PA.ActualRefutationGraph.formula_graph]
  exact refutation_implies_blank

theorem pa_proves_nonhalting_no_actual_refutation :
    theory ⊢ HaltingFormula.nonhaltingSentence 🡒 noActualRefutationSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [models_iff,LogicalConnective.HomClass.map_imply]
  simp [HaltingFormula.nonhaltingSentence,noActualRefutationSentence,
    M6.PA.ActualRefutationGraph.formula_graph]
  intro hn code hc
  exact hn (refutation_implies_blank code hc)
#print axioms refutation_implies_blank
#print axioms pa_proves_refutation_halting
#print axioms pa_proves_nonhalting_no_actual_refutation
end M6.Arithmetic.PA.InternalActualRefutation
