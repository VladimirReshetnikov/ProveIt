module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceMP
public import M6PA.Scheduler.ActualCommandMPInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- HFS4 execution state projected from the distinct full logical HFS9 store. -/
noncomputable def commandState (xs : V) : V :=
  ActualCommandStepGraph.stateCode (registers xs 1) (registers xs 2) (registers xs 4) (registers xs 5)

noncomputable def commandObservation (c : V) : V :=
  if control c=0 then 0 else commandState (store c)

@[simp] theorem commandObservation_halt (xs : V) : commandObservation (stateCode 0 xs)=0 := by
  simp [commandObservation,control,stateCode]
@[simp] theorem commandObservation_root (xs : V) : commandObservation (stateCode 1 xs)=commandState xs := by
  simp [commandObservation,control,store,stateCode]

theorem s36_command_projection (xs : V) (hv : ValidStore xs) :
    commandObservation (if registers xs 1+registers xs 5=1 then stateCode 0 (s36GuardEnd xs) else stateCode 1 (s36End xs))=
      ActualCommandStepGraph.stepValue 0 (commandState xs) := by
  rw [commandState,ActualCommandStepGraph.shift_value]
  by_cases h : registers xs 1+registers xs 5=1
  · simp only [h,ite_true,commandObservation_halt]
  · simp only [h,ite_false,commandObservation_root,commandState,s36End_effect xs hv]
    simp [PhysicalRegisters.write]

theorem mp_command_projection (xs : V) (hv : ValidStore xs) :
    commandState (mpEnd xs)=ActualCommandStepGraph.stepValue
      (ActualCommandStepGraph.mpCode (decodeLeft (registers xs 8))) (commandState xs) := by
  rw [commandState,mpEnd_effect xs hv,commandState,ActualCommandStepGraph.mp_value]
  simp only [ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval,Nat.cast_ofNat]
  by_cases h : mpConstructor xs=registers xs 5 <;>
    simp_all [PhysicalRegisters.write,mpConstructor,mpOffset]
#print axioms s36_command_projection
#print axioms mp_command_projection
end M6.Arithmetic.PA.InternalTrace.CodedSource

