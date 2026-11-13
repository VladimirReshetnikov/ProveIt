module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceLoopRegisters
public import PA196.Arithmetic.Scheduler.InternalCodedSourceTraceCompose
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrainSpec
public import PA196.Source.Dispatch
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem dispatch_zero (xs : V) (ha : registers xs 3=0) :
    Trace 1 ?[stateCode 49 xs,stateCode 3801 xs] (stateCode 49 xs) (stateCode 3801 xs) := by
  have hs : stepValue (stateCode 49 xs)=stateCode 3801 xs := by
    have h := literal_step 48 (by decide) _ PA196.Source.Dispatch.resolve_48 xs
    simpa [instructionValue,destinationCode,ha] using h
  simpa only [hs] using trace_one (stateCode 49 xs)

theorem dispatch_one (xs : V) (hv : ValidStore xs) (ha : registers xs 3=1) :
    ∃cs,Trace 2 cs (stateCode 49 xs) (stateCode 3694 (replace 3 xs 0)) := by
  have hs : stepValue (stateCode 49 xs)=stateCode 50 (replace 3 xs 0) := by
    have h := literal_step 48 (by decide) _ PA196.Source.Dispatch.resolve_48 xs
    simpa [instructionValue,destinationCode,ha] using h
  have hz : registers (replace 3 xs 0) 3=0 := registers_replace_same xs 0 hv 3
  have ht : stepValue (stateCode 50 (replace 3 xs 0))=stateCode 3694 (replace 3 xs 0) := by
    have h := literal_step 49 (by decide) _ PA196.Source.Dispatch.resolve_49 (replace 3 xs 0)
    simpa [instructionValue,destinationCode,hz] using h
  have tr : Trace 1 ?[stateCode 50 (replace 3 xs 0),stateCode 3694 (replace 3 xs 0)]
      (stateCode 50 (replace 3 xs 0)) (stateCode 3694 (replace 3 xs 0)) := by
    simpa only [ht] using trace_one (stateCode 50 (replace 3 xs 0))
  simpa only [one_add_one_eq_two] using trace_prepend _ hs tr

theorem dispatch_many (xs a : V) (hv : ValidStore xs) (ha : registers xs 3=(a+1)+1) :
    ∃cs,Trace 2 cs (stateCode 49 xs) (stateCode 51 (replace 3 xs a)) := by
  have hs : stepValue (stateCode 49 xs)=stateCode 50 (replace 3 xs (a+1)) := by
    have h := literal_step 48 (by decide) _ PA196.Source.Dispatch.resolve_48 xs
    simpa [instructionValue,destinationCode,ha] using h
  have hz : registers (replace 3 xs (a+1)) 3=a+1 := registers_replace_same xs _ hv 3
  have ht : stepValue (stateCode 50 (replace 3 xs (a+1)))=stateCode 51 (replace 3 xs a) := by
    have h := literal_step 49 (by decide) _ PA196.Source.Dispatch.resolve_49 (replace 3 xs (a+1))
    simpa [instructionValue,destinationCode,hz,replace_same] using h
  have tr : Trace 1 ?[stateCode 50 (replace 3 xs (a+1)),stateCode 51 (replace 3 xs a)]
      (stateCode 50 (replace 3 xs (a+1))) (stateCode 51 (replace 3 xs a)) := by
    simpa only [ht] using trace_one (stateCode 50 (replace 3 xs (a+1)))
  simpa only [one_add_one_eq_two] using trace_prepend _ hs tr
#print axioms dispatch_zero
#print axioms dispatch_one
#print axioms dispatch_many
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

