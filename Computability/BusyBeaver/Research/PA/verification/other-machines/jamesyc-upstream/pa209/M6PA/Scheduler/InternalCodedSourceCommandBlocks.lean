module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCommandProjection
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Only source scratch/selector registers are clean; command caches D/H may be arbitrary. -/
def CommandClean (xs : V) : Prop := registers xs 3=0 ∧ registers xs 6=0 ∧ registers xs 7=0
noncomputable def shiftOutcome (xs : V) : V :=
  if registers xs 1+registers xs 5=1 then stateCode 0 (s36GuardEnd xs) else stateCode 1 (s36End xs)

theorem shiftOutcome_trace (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 3912 xs) (shiftOutcome xs) :=
  actual_s36 xs hv hc.2.1 hc.2.2

theorem shiftOutcome_command (xs : V) (hv : ValidStore xs) :
    commandObservation (shiftOutcome xs)=ActualCommandStepGraph.stepValue 0 (commandState xs) :=
  s36_command_projection xs hv

theorem shiftOutcome_valid (xs : V) (hv : ValidStore xs) : ValidStore (store (shiftOutcome xs)) := by
  unfold shiftOutcome
  split
  · simpa [store,stateCode] using s36GuardEnd_valid xs hv
  · simpa [store,stateCode,s36End] using unpairFullEnd_valid 2 6 7 5 (s36GuardEnd xs) (registers xs 2) (s36GuardEnd_valid xs hv)

theorem shiftOutcome_clean (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) : CommandClean (store (shiftOutcome xs)) := by
  unfold shiftOutcome
  split <;> simp only [store_state]
  · rw [CommandClean,s36GuardEnd_effect xs hv]
    simp [PhysicalRegisters.write,hc.1,hc.2.2]
  · rw [CommandClean,s36End_effect xs hv]
    simp [PhysicalRegisters.write,hc.1]

theorem shiftOutcome_frame (xs : V) (hv : ValidStore xs) :
    registers (store (shiftOutcome xs)) 0=registers xs 0 ∧
    registers (store (shiftOutcome xs)) 8=registers xs 8 := by
  unfold shiftOutcome
  split <;> simp only [store_state]
  · rw [s36GuardEnd_effect xs hv]; simp [PhysicalRegisters.write]
  · rw [s36End_effect xs hv]; simp [PhysicalRegisters.write]

theorem shiftOutcome_control (xs : V) : control (shiftOutcome xs)=0 ∨ control (shiftOutcome xs)=1 := by
  unfold shiftOutcome
  split <;> simp [control,stateCode]

theorem mpEnd_clean (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) : CommandClean (mpEnd xs) := by
  rw [CommandClean,mpEnd_effect xs hv]
  simp [PhysicalRegisters.write,hc.1]

theorem mpEnd_frame (xs : V) (hv : ValidStore xs) :
    registers (mpEnd xs) 0=registers xs 0 ∧
    registers (mpEnd xs) 8=SourceCantorInternal.decodeRight (registers xs 8) := by
  rw [mpEnd_effect xs hv]; simp [PhysicalRegisters.write]
#print axioms shiftOutcome_valid
#print axioms shiftOutcome_clean
#print axioms shiftOutcome_frame
#print axioms mpEnd_clean
end M6.Arithmetic.PA.InternalTrace.CodedSource

