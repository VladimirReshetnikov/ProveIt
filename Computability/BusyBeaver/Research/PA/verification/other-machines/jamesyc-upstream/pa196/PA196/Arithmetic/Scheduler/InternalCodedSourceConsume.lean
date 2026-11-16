module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceRootCommand
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCommandIteration
public import PA196.Arithmetic.Scheduler.InternalCodedSourceExt
public import PA196.Arithmetic.Scheduler.SourceCommandResidualTermination
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCommandEncodingInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

/-- A residual command is simulated literally; finished residuals and already
halted arithmetic execution may use a zero-length source trace. -/
theorem source_consume_step (c n p : V) (h : TraversalRelation c n p) :
    ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consumeStep p) := by
  by_cases hz : p.[0]=0
  · exact ⟨0,?[c],c,trace_zero c,by simpa only [consumeStep,hz,ite_true] using h⟩
  · rcases h with hh|⟨hp,hv,hc,hn,hl,hs⟩
    · have hout : (consumeStep p).[1]=0 := by
        simp [consumeStep,hz,hh.1,traversal_second]
      refine ⟨0,?[c],c,trace_zero c,?_⟩
      change CommandRelation c n (consumeStep p).[0] (consumeStep p).[1]
      rw [hout]
      exact commandRelation_halt _ _ _ hh.2
    · rcases zero_or_succ p.[0] with he|⟨raw,he⟩
      · exact False.elim (hz he)
      · have hl' : registers (store c) 8=raw+1 := hl.trans he
        obtain ⟨k,cs,d,hk,ht,hr⟩ := root_positive_command (store c) raw hv hc hl'
        have ec : stateCode 26 (store c)=c := by simpa only [hp] using state_reconstruct hv
        rw [ec] at ht
        rw [hn,hs] at hr
        have ep : consumeStep p=traversalState (residual raw)
            (CommandStep.stepValue (commandAtom raw) p.[1]) := by
          simp [consumeStep,he]
        refine ⟨k,cs,d,ht,?_⟩
        simpa only [TraversalRelation,ep,traversal_first,traversal_second] using hr

/-- Closed literal refinement of the already-fixed model-valued consume graph. -/
theorem source_consume (i c n p : V) (h : TraversalRelation c n p) :
    ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consume i p) :=
  command_trace_iteration source_consume_step i c n p h
#print axioms source_consume_step
#print axioms source_consume
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

