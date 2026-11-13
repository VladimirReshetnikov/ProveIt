module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXCommandStore
public import M6PA.Scheduler.InternalCodedSourceCommandBlockRelation
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def dispatchAXStore (xs a : V) : V := replace 3 xs a
noncomputable def dispatchAXEnd (xs a : V) : V := axEnd (dispatchAXStore xs a)
lemma dispatchAXStore_registers (xs a : V) (hv : ValidStore xs) :
    registers (dispatchAXStore xs a)=PhysicalRegisters.write (registers xs) 3 a := registers_replace xs a hv 3
lemma dispatchAXStore_command (xs a : V) (hv : ValidStore xs) :
    commandState (dispatchAXStore xs a)=commandState xs := by
  simp [commandState,dispatchAXStore_registers xs a hv,PhysicalRegisters.write]

theorem dispatch_ax (xs a : V) (hv : ValidStore xs) (ha : registers xs 3=(a+1)+1)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 24 xs) (stateCode 1 (dispatchAXEnd xs a)) := by
  have hv' : ValidStore (dispatchAXStore xs a) := replace_valid xs a hv 3
  have hx' : registers (dispatchAXStore xs a) 6=0 := by rw [dispatchAXStore_registers xs a hv]; simp [PhysicalRegisters.write,hx]
  have hy' : registers (dispatchAXStore xs a) 7=0 := by rw [dispatchAXStore_registers xs a hv]; simp [PhysicalRegisters.write,hy]
  obtain ⟨ps,hp⟩ := dispatch_many xs a hv ha
  obtain ⟨n,cs,hn,ht⟩ := ax_block (dispatchAXStore xs a) hv' hx' hy'
  obtain ⟨ds,hd⟩ := trace_compose hp ht
  obtain ⟨es,he⟩ := trace_compose hd (mp_return_trace (dispatchAXEnd xs a))
  exact ⟨2+n+1,es,by simp,he⟩

theorem dispatchAXEnd_relation (xs a : V) (hv : ValidStore xs) :
    CommandRelation (stateCode 1 (dispatchAXEnd xs a)) (registers xs 0)
      (decodeRight (decodeRight (registers xs 8)))
      (ActualCommandStepGraph.stepValue
        (ActualCommandStepGraph.axCode a (decodeLeft (decodeRight (registers xs 8))) (decodeLeft (registers xs 8)))
        (commandState xs)) := by
  have fr := axEnd_frame (dispatchAXStore xs a)
  have clean : CommandClean (dispatchAXEnd xs a) := ⟨fr.2.2.1,fr.2.2.2.2.2.1,fr.2.2.2.2.2.2⟩
  have h := commandRelation_root (dispatchAXEnd xs a) (axEnd_valid _) clean
  have e := ax_command_projection (dispatchAXStore xs a)
  change commandState (dispatchAXEnd xs a)=_ at e
  have fn : registers (dispatchAXEnd xs a) 0=registers (dispatchAXStore xs a) 0 := fr.1
  have fl : registers (dispatchAXEnd xs a) 8=decodeRight (decodeRight (registers (dispatchAXStore xs a) 8)) := fr.2.1
  rw [fn,fl,e,dispatchAXStore_command xs a hv,dispatchAXStore_registers xs a hv] at h
  simpa [PhysicalRegisters.write] using h
#print axioms dispatch_ax
#print axioms dispatchAXEnd_relation
end M6.Arithmetic.PA.InternalTrace.CodedSource

