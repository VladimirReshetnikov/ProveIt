module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceConsume
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCommandEncodingInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem candidateRun_halted (n : V) : candidateRun n 0=0 := consume_halted (n+1) (n+1)

/-- Starting candidate n uses a fresh source L0 branch, followed by n further
bounded consume steps: exactly n+1 commands, never a truncated suffix. -/
theorem source_candidate (c n initial : V) (h : CommandRelation c n 0 initial) :
    ∃k cs d,Trace k cs c d ∧ CommandRelation d (n+1) 0 (candidateRun n initial) := by
  rcases h with hh|⟨hp,hv,hc,hn,hl,hs⟩
  · refine ⟨0,?[c],c,trace_zero c,?_⟩
    rw [hh.1,candidateRun_halted]
    exact commandRelation_halt _ _ _ hh.2
  · obtain ⟨m,ps,d,hm,ht,hr⟩ := root_fresh_command (store c) hv hc hl
    have ec : stateCode 26 (store c)=c := by simpa only [hp] using state_reconstruct hv
    rw [ec] at ht
    rw [hn,hs] at hr
    have hd : TraversalRelation d (n+1) (consumeStep (traversalState (n+1) initial)) := by
      simpa only [consume_positive_step,TraversalRelation,traversal_first,traversal_second] using hr
    obtain ⟨k,cs,e,hk,he⟩ := source_consume n d (n+1) _ hd
    rw [←consume_succ_start,every_candidate_result] at he
    obtain ⟨ds,hds⟩ := trace_compose ht hk
    refine ⟨m+k,ds,e,hds,?_⟩
    simpa only [TraversalRelation,traversal_first,traversal_second] using he

lemma commandRelation_zero (c n l : V) (h : CommandRelation c n l 0) : control c=0 := by
  rcases h with h|⟨_,_,_,_,_,hs⟩
  · exact h.2
  · exact False.elim ((CommandStep.stateCode_ne_zero _ _ _ _) hs)
#print axioms source_candidate
#print axioms commandRelation_zero
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

