module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceDrain
public import M6.Source.S36Binding
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- The actual three source leaves at ordinals3911--3913 drain T into X.
The counter and entire logical store may be nonstandard. -/
theorem actual_s36_drain_T (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode 3912 xs) (stateCode 3915 (drainEnd 1 6 n xs)) := by
  apply drain_loop 3911 3912 3913 3914 1 6 (by decide)
    (by decide) (by decide) (by decide)
  · exact Source.s36_resolved_at ⟨0,by decide⟩
  · exact Source.s36_resolved_at ⟨1,by decide⟩
  · exact Source.s36_resolved_at ⟨2,by decide⟩
  · exact hv
  · exact ht

/-- The actual final three drain leaves restore X into H. -/
theorem actual_s36_drain_X (n xs : V) (hv : ValidStore xs) (ht : registers xs 6=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode 3919 xs) (stateCode 3922 (drainEnd 6 5 n xs)) := by
  apply drain_loop 3918 3919 3920 3921 6 5 (by decide)
    (by decide) (by decide) (by decide)
  · exact Source.s36_resolved_at ⟨7,by decide⟩
  · exact Source.s36_resolved_at ⟨8,by decide⟩
  · exact Source.s36_resolved_at ⟨9,by decide⟩
  · exact hv
  · exact ht
#print axioms actual_s36_drain_T
#print axioms actual_s36_drain_X
end M6.Arithmetic.PA.InternalTrace.CodedSource

