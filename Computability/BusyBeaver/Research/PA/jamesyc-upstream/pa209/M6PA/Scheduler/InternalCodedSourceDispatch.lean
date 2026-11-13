module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceLoopRegisters
public import M6PA.Scheduler.InternalCodedSourceTraceCompose
public import M6PA.Scheduler.InternalCodedSourceDrainSpec
public import M6.Source.Dispatch
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem dispatch_zero (xs : V) (ha : registers xs 3=0) :
    Trace 1 ?[stateCode 24 xs,stateCode 3912 xs] (stateCode 24 xs) (stateCode 3912 xs) := by
  have hs : stepValue (stateCode 24 xs)=stateCode 3912 xs := by
    have h := literal_step 23 (by decide) _ Source.Dispatch.resolve_23 xs
    simpa [instructionValue,destinationCode,ha] using h
  simpa only [hs] using trace_one (stateCode 24 xs)

theorem dispatch_one (xs : V) (hv : ValidStore xs) (ha : registers xs 3=1) :
    ∃cs,Trace 2 cs (stateCode 24 xs) (stateCode 3805 (replace 3 xs 0)) := by
  have hs : stepValue (stateCode 24 xs)=stateCode 25 (replace 3 xs 0) := by
    have h := literal_step 23 (by decide) _ Source.Dispatch.resolve_23 xs
    simpa [instructionValue,destinationCode,ha] using h
  have hz : registers (replace 3 xs 0) 3=0 := registers_replace_same xs 0 hv 3
  have ht : stepValue (stateCode 25 (replace 3 xs 0))=stateCode 3805 (replace 3 xs 0) := by
    have h := literal_step 24 (by decide) _ Source.Dispatch.resolve_24 (replace 3 xs 0)
    simpa [instructionValue,destinationCode,hz] using h
  have tr : Trace 1 ?[stateCode 25 (replace 3 xs 0),stateCode 3805 (replace 3 xs 0)]
      (stateCode 25 (replace 3 xs 0)) (stateCode 3805 (replace 3 xs 0)) := by
    simpa only [ht] using trace_one (stateCode 25 (replace 3 xs 0))
  simpa only [one_add_one_eq_two] using trace_prepend _ hs tr

theorem dispatch_many (xs a : V) (hv : ValidStore xs) (ha : registers xs 3=(a+1)+1) :
    ∃cs,Trace 2 cs (stateCode 24 xs) (stateCode 26 (replace 3 xs a)) := by
  have hs : stepValue (stateCode 24 xs)=stateCode 25 (replace 3 xs (a+1)) := by
    have h := literal_step 23 (by decide) _ Source.Dispatch.resolve_23 xs
    simpa [instructionValue,destinationCode,ha] using h
  have hz : registers (replace 3 xs (a+1)) 3=a+1 := registers_replace_same xs _ hv 3
  have ht : stepValue (stateCode 25 (replace 3 xs (a+1)))=stateCode 26 (replace 3 xs a) := by
    have h := literal_step 24 (by decide) _ Source.Dispatch.resolve_24 (replace 3 xs (a+1))
    simpa [instructionValue,destinationCode,hz,replace_same] using h
  have tr : Trace 1 ?[stateCode 25 (replace 3 xs (a+1)),stateCode 26 (replace 3 xs a)]
      (stateCode 25 (replace 3 xs (a+1))) (stateCode 26 (replace 3 xs a)) := by
    simpa only [ht] using trace_one (stateCode 25 (replace 3 xs (a+1)))
  simpa only [one_add_one_eq_two] using trace_prepend _ hs tr
#print axioms dispatch_zero
#print axioms dispatch_one
#print axioms dispatch_many
end M6.Arithmetic.PA.InternalTrace.CodedSource

