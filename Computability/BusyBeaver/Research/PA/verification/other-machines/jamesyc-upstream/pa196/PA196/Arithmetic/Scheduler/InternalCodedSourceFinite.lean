module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrainSpec
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def finiteRun : Nat → V → V
  | 0,a => a
  | n+1,a => finiteRun n (stepValue a)
theorem finiteRun_trace (n : Nat) (a : V) : ∃ cs,Trace (n:V) cs a (finiteRun n a) := by
  induction n generalizing a with
  | zero => exact ⟨?[a],by simpa [finiteRun] using trace_zero a⟩
  | succ n ih =>
    obtain ⟨cs,h⟩ := ih (stepValue a)
    obtain ⟨ds,hd⟩ := trace_prepend a rfl h
    exact ⟨ds,by simpa only [Nat.cast_add,Nat.cast_one,finiteRun] using hd⟩
#print axioms finiteRun_trace
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

