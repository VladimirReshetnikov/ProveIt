module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrain
public import PA196.Source.S36Binding
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

/-- The actual three source leaves at ordinals3911--3802 drain T into X.
The counter and entire logical store may be nonstandard. -/
theorem actual_s36_drain_T (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode 3801 xs) (stateCode 3804 (drainEnd 1 6 n xs)) := by
  apply drain_loop 3800 3801 3802 3803 1 6 (by decide)
    (by decide) (by decide) (by decide)
  · exact PA196.Source.s36_resolved_at ⟨0,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨1,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨2,by decide⟩
  · exact hv
  · exact ht

/-- The actual final three drain leaves restore X into H. -/
theorem actual_s36_drain_X (n xs : V) (hv : ValidStore xs) (ht : registers xs 6=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode 3808 xs) (stateCode 3811 (drainEnd 6 5 n xs)) := by
  apply drain_loop 3807 3808 3809 3810 6 5 (by decide)
    (by decide) (by decide) (by decide)
  · exact PA196.Source.s36_resolved_at ⟨7,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨8,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨9,by decide⟩
  · exact hv
  · exact ht
#print axioms actual_s36_drain_T
#print axioms actual_s36_drain_X
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

