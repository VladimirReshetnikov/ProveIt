module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDispatchAX
public import PA196.Arithmetic.Scheduler.SourceCommandDecodeInternal
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal SourceCommandEncodingInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem dispatch_command (xs raw : V) (hv : ValidStore xs)
    (ha : registers xs 3=decodeLeft raw) (hl : registers xs 8=decodeRight raw)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃k cs d,0<k ∧ Trace k cs (stateCode 49 xs) d ∧
      CommandRelation d (registers xs 0) (residual raw)
        (CommandStep.stepValue (commandAtom raw) (commandState xs)) := by
  rcases zero_or_succ (decodeLeft raw) with hzero | ⟨a,hsucc⟩
  · have hc : CommandClean xs := ⟨ha.trans hzero,hx,hy⟩
    obtain ⟨k,cs,hk,ht⟩ := dispatch_shift xs hv hc
    have hr := shiftOutcome_relation xs hv hc
    rw [hl] at hr
    refine ⟨k,cs,shiftOutcome xs,hk,ht,?_⟩
    simpa [residual,commandAtom,hzero] using hr
  · rcases zero_or_succ a with azero | ⟨b,asucc⟩
    · have hone : decodeLeft raw=1 := by simpa only [azero,zero_add] using hsucc
      obtain ⟨k,cs,hk,ht⟩ := dispatch_mp xs hv (ha.trans hone) hx hy
      have hr := dispatchMPEnd_relation xs hv hx hy
      rw [hl] at hr
      refine ⟨k,cs,stateCode 26 (dispatchMPEnd xs),hk,ht,?_⟩
      simpa [residual,commandAtom,hone,CommandStep.mpCode] using hr
    · have hmany : decodeLeft raw=(b+1)+1 := by simpa only [asucc] using hsucc
      obtain ⟨k,cs,hk,ht⟩ := dispatch_ax xs b hv (ha.trans hmany) hx hy
      have hr := dispatchAXEnd_relation xs b hv
      rw [hl] at hr
      refine ⟨k,cs,stateCode 26 (dispatchAXEnd xs b),hk,ht,?_⟩
      have hn : (b+1)+1≠1 := by simp
      have hn2 : b+2≠1 := by simpa only [add_assoc,one_add_one_eq_two] using hn
      simpa [residual,commandAtom,hmany,CommandStep.axCode,add_assoc,one_add_one_eq_two,hn2] using hr
#print axioms dispatch_command
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

