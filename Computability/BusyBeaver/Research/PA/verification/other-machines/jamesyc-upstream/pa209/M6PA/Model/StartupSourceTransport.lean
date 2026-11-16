module
public import M6PA.Model.EndpointInternalStartupFrame
public import M6PA.Model.EndpointInternalCodedSourcePhysicalTrace
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CodedSource
section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- A model-length halt of the retained original source from the actual N=2
clean startup forces a literal-209 arithmetic machine halt from blank tape.
The exact 26-spare file, extra return, and full nonstandard file are retained. -/
theorem source_halt_blank {n cs b : V}
    (h : Trace n cs (entryState (V := V)) b) (hb : control b=0) :
    ∃ k qs ls rs lf rf : V, 0<k ∧ Segment k qs ls rs 0 0 0 215 lf rf := by
  obtain ⟨qs,ls,rs,hstart⟩ := startup_all_models (V := V)
  obtain ⟨k,qs',ls',rs',lf,rf,hpos,hhalt⟩ :=
    trace_halt_physical h (startup_refines_all_models (V := V)) hb
  obtain ⟨qall,lall,rall,hall⟩ := segment_compose hstart hhalt
  exact ⟨58210+k,qall,lall,rall,lf,rf,
    lt_of_lt_of_le hpos (by simp),hall⟩
end Models

def startupSourceHaltingSentence : ArithmeticSentence :=
  “∀ n cs b regs c,
    !(fixedFileGraph startupRegisters) regs ∧ !adjoinDef c 1 regs ∧
    !traceGraph n cs c b ∧ !fstIdxDef 0 b →
    ∃ k qs ls rs lf rf, 0<k ∧ !segmentFormula k qs ls rs 0 0 0 215 lf rf”

theorem pa_proves_startup_source_transport : theory ⊢ startupSourceHaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [startupSourceHaltingSentence,models_iff]
  simp [fixedFile_correct,adjoin_defined.df,trace_correct,fstIdx_defined.df,segment_correct]
  intro n cs b ht hb
  simpa [entryState,stateCode,numeral_eq_natCast,Nat.cast_ofNat] using
    source_halt_blank (V := V) ht (by simpa only [CodedSource.control,eq_comm] using hb)
#print axioms source_halt_blank
#print axioms pa_proves_startup_source_transport
end M6.Arithmetic.PA.InternalTrace.FixedTrace
