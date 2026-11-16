module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCommandBlocks
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDispatch
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem dispatch_shift (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 49 xs) (shiftOutcome xs) := by
  obtain ⟨n,cs,hn,ht⟩ := shiftOutcome_trace xs hv hc
  obtain ⟨ds,hd⟩ := trace_compose (dispatch_zero xs hc.1) ht
  exact ⟨1+n,ds,by simp,hd⟩

noncomputable def dispatchMPStore (xs : V) : V := replace 3 xs 0
noncomputable def dispatchMPEnd (xs : V) : V := mpEnd (dispatchMPStore xs)

theorem dispatchMPStore_valid (xs : V) (hv : ValidStore xs) : ValidStore (dispatchMPStore xs) := replace_valid xs 0 hv 3

theorem dispatchMPStore_registers (xs : V) (hv : ValidStore xs) :
    registers (dispatchMPStore xs)=PhysicalRegisters.write (registers xs) 3 0 := registers_replace xs 0 hv 3

theorem dispatchMPStore_clean (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) : CommandClean (dispatchMPStore xs) := by
  rw [CommandClean,dispatchMPStore_registers xs hv]
  simp [PhysicalRegisters.write,hx,hy]

theorem dispatchMPStore_command (xs : V) (hv : ValidStore xs) : commandState (dispatchMPStore xs)=commandState xs := by
  simp [commandState,dispatchMPStore_registers xs hv,PhysicalRegisters.write]

theorem dispatch_mp (xs : V) (hv : ValidStore xs) (ha : registers xs 3=1)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 49 xs) (stateCode 26 (dispatchMPEnd xs)) := by
  have clean := dispatchMPStore_clean xs hv hx hy
  obtain ⟨ps,hp⟩ := dispatch_one xs hv ha
  obtain ⟨n,cs,hn,ht⟩ := actual_mp (dispatchMPStore xs) (dispatchMPStore_valid xs hv) clean.2.1 clean.2.2
  obtain ⟨ds,hd⟩ := trace_compose hp ht
  exact ⟨2+n,ds,lt_of_lt_of_le hn (by simp),hd⟩

theorem dispatchMPEnd_command (xs : V) (hv : ValidStore xs) :
    commandState (dispatchMPEnd xs)=CommandStep.stepValue
      (CommandStep.mpCode (decodeLeft (registers xs 8))) (commandState xs) := by
  rw [dispatchMPEnd,mp_command_projection _ (dispatchMPStore_valid xs hv),dispatchMPStore_command xs hv,
    dispatchMPStore_registers xs hv]
  simp [PhysicalRegisters.write]

theorem dispatchMPEnd_frame (xs : V) (hv : ValidStore xs) :
    registers (dispatchMPEnd xs) 0=registers xs 0 ∧
    registers (dispatchMPEnd xs) 8=decodeRight (registers xs 8) := by
  have h := mpEnd_frame (dispatchMPStore xs) (dispatchMPStore_valid xs hv)
  simpa only [dispatchMPEnd,dispatchMPStore_registers xs hv,PhysicalRegisters.write,show (0:Fin 9)≠3 by decide,
    show (8:Fin 9)≠3 by decide,ite_false] using h
#print axioms dispatch_shift
#print axioms dispatch_mp
#print axioms dispatchMPEnd_command
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

