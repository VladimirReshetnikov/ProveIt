module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCommandProjection
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

/-- Only source scratch/selector registers are clean; command caches D/H may be arbitrary. -/
def CommandClean (xs : V) : Prop := registers xs 3=0 ∧ registers xs 6=0 ∧ registers xs 7=0
noncomputable def shiftOutcome (xs : V) : V :=
  if registers xs 1+registers xs 5=1 then stateCode 0 (s36GuardEnd xs) else stateCode 26 (s36End xs)

theorem shiftOutcome_trace (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 3801 xs) (shiftOutcome xs) :=
  actual_s36 xs hv hc.2.1 hc.2.2

theorem shiftOutcome_command (xs : V) (hv : ValidStore xs) :
    commandObservation (shiftOutcome xs)=CommandStep.stepValue 0 (commandState xs) :=
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

theorem shiftOutcome_control (xs : V) : control (shiftOutcome xs)=0 ∨ control (shiftOutcome xs)=26 := by
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
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

