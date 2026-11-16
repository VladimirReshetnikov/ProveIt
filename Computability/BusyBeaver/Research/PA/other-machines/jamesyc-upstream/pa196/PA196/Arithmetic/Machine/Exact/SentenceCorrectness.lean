module
public import PA196.Arithmetic.Machine.Exact.EndpointTraceAdequacy
public import PA196.Arithmetic.Machine.Exact.EndpointPaddedNatTape
public import PA196.Startup.Data
@[expose] public section
namespace PA196.Arithmetic.Machine.Exact.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Each of the 392 arithmetic rows is the corresponding literal transition,
with working labels 0..195 and the unique undefined terminal label 196. -/
theorem literal_binding : ∀ (q : WorkingState) (b : Bool),
    PA196.Literal.machine q.val b = some ((row q b).write,(row q b).right,
      StepFormula.controlCode (row q b).next) := by
  decide +kernel

theorem root_code : StepFormula.controlCode dispatcher=75 := rfl
theorem halt_code : StepFormula.controlCode halt=196 := rfl

/-- Standard truth of this explicit first-order arithmetic sentence is exactly
nonhalting of the 196-state table on the blank tape. -/
theorem sentence_iff_literal_nonhalting :
    (Nat ⊧/![] HaltingFormula.nonhaltingSentence) ↔
      ¬ M6.Zip.Halts PA196.Literal.machine PA196.Startup.blank := by
  have hp := PaddedBridge.halts_iff PaddedNatTape.nativeBlank
    (Or.inr PA196.Literal.start_working)
  have hn := PaddedNatTape.native_blank_halts_iff
  exact HaltingFormula.nonhaltingSentence_iff.trans (not_congr (hn.symm.trans hp))

#print axioms literal_binding
#print axioms sentence_iff_literal_nonhalting
end PA196.Arithmetic.Machine.Exact.PA
