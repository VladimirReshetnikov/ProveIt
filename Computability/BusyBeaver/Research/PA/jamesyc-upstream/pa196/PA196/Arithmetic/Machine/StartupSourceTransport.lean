module
public import PA196.Arithmetic.Machine.EndpointInternalStartupFrame
public import PA196.Arithmetic.Machine.EndpointInternalCodedSourcePhysicalTrace
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CodedSource
section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- A model-length halt of the exact PA196 source from the actual N=2
clean startup forces an auxiliary arithmetic machine halt from blank tape.
The exact 26-spare file, extra return, and full nonstandard file are retained. -/
theorem source_halt_blank {n cs b : V}
    (h : Trace n cs (entryState (V := V)) b) (hb : control b=0) :
    ∃ k qs ls rs lf rf : V, 0<k ∧ Segment k qs ls rs 0 0 0 215 lf rf := by
  obtain ⟨qs,ls,rs,hstart⟩ := startup_all_models (V := V)
  obtain ⟨k,qs',ls',rs',lf,rf,hpos,hhalt⟩ :=
    trace_halt_physical h (startup_refines_all_models (V := V)) hb
  obtain ⟨qall,lall,rall,hall⟩ := segment_compose hstart hhalt
  exact ⟨58154+k,qall,lall,rall,lf,rf,
    lt_of_lt_of_le hpos (by simp),hall⟩
end Models

def startupSourceHaltingSentence : ArithmeticSentence :=
  “∀ n cs b regs c,
    !(fixedFileGraph startupRegisters) regs ∧ !adjoinDef c 26 regs ∧
    !traceGraph n cs c b ∧ !fstIdxDef 0 b →
    ∃ k qs ls rs lf rf, 0<k ∧ !segmentFormula k qs ls rs 0 0 0 215 lf rf”

attribute [local irreducible] stepValue stepGraph traceGraph Trace Segment segmentFormula StepFormula.formula

theorem pa_proves_startup_source_transport : theory ⊢ startupSourceHaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [startupSourceHaltingSentence,models_iff]
  simp [fixedFile_correct,adjoin_defined.df,trace_correct,fstIdx_defined.df,segment_correct]
  intro n cs b ht hb
  simpa [entryState,stateCode,numeral_eq_natCast,Nat.cast_ofNat] using
    source_halt_blank (V := V) (by simpa only [entryState,stateCode,numeral_eq_natCast,Nat.cast_ofNat] using ht)
      (by simpa only [CodedSource.control,eq_comm] using hb)
#print axioms source_halt_blank
#print axioms pa_proves_startup_source_transport
end PA196.Arithmetic.Machine.PA.InternalTrace.FixedTrace
