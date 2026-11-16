module
public import PA196.Arithmetic.Machine.StartupSourceTransport
public import PA196.Arithmetic.Machine.StateMapProjection
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CodedSource

section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- An internally coded halt of the exact PA196 source, starting with the
proved startup register file, implies the 392-row literal arithmetic halt
sentence in the same PA model. -/
theorem source_halt_literal {n cs b : V}
    (h : Trace n cs (entryState (V := V)) b) (hb : control b=0) :
    V ⊧/![] Exact.PA.HaltingFormula.traceSentence := by
  obtain ⟨k,qs,ls,rs,lf,rf,_,hseg⟩ := source_halt_blank h hb
  exact StateMap.segment_to_literal hseg

end Models

def literalStartupSourceHaltingSentence : ArithmeticSentence :=
  “∀ n cs b regs c,
    !(fixedFileGraph startupRegisters) regs ∧ !adjoinDef c 26 regs ∧
    !traceGraph n cs c b ∧ !fstIdxDef 0 b → !Exact.PA.HaltingFormula.traceSentence”

attribute [local irreducible] Exact.PA.HaltingFormula.traceSentence stepValue stepGraph traceGraph Trace

theorem pa_proves_literal_startup_source_transport : theory ⊢ literalStartupSourceHaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [literalStartupSourceHaltingSentence,models_iff]
  simp [fixedFile_correct,adjoin_defined.df,trace_correct,fstIdx_defined.df]
  intro n cs b ht hb
  apply source_halt_literal (V := V) (n := n) (cs := cs) (b := b) ?_ ?_
  · simpa [entryState,stateCode,numeral_eq_natCast,Nat.cast_ofNat] using ht
  · simpa only [CodedSource.control,eq_comm] using hb

#print axioms source_halt_literal
#print axioms pa_proves_literal_startup_source_transport
end PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace
