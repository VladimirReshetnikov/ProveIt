module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceDispatchTotal
public import M6PA.Scheduler.InternalCodedSourceFetch
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal SourceCommandEncodingInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem root_positive_command (xs raw : V) (hv : ValidStore xs) (hc : CommandClean xs)
    (hl : registers xs 8=raw+1) :
    ∃k cs d,0<k ∧ Trace k cs (stateCode 1 xs) d ∧
      CommandRelation d (registers xs 0) (residual raw)
        (ActualCommandStepGraph.stepValue (commandAtom raw) (commandState xs)) := by
  have fv : ValidStore (fetchPositiveEnd xs raw) := fetchDecodeEnd_valid _ (replace_valid xs raw hv 8)
  have ef := fetchPositiveEnd_effect xs raw hv
  have fa : registers (fetchPositiveEnd xs raw) 3=decodeLeft raw := by rw [ef]; simp [PhysicalRegisters.write,hc.1]
  have fl : registers (fetchPositiveEnd xs raw) 8=decodeRight raw := by rw [ef]; simp [PhysicalRegisters.write]
  have fx : registers (fetchPositiveEnd xs raw) 6=0 := by rw [ef]; simp [PhysicalRegisters.write]
  have fy : registers (fetchPositiveEnd xs raw) 7=0 := by rw [ef]; simp [PhysicalRegisters.write]
  have fn : registers (fetchPositiveEnd xs raw) 0=registers xs 0 := by rw [ef]; simp [PhysicalRegisters.write]
  obtain ⟨m,ps,hm,hp⟩ := fetch_positive_complete xs raw hv hl hc.2.1 hc.2.2
  obtain ⟨k,cs,d,hk,ht,hr⟩ := dispatch_command (fetchPositiveEnd xs raw) raw fv fa fl fx fy
  rw [fn,fetchPositiveEnd_commandState xs raw hv] at hr
  obtain ⟨ds,hd⟩ := trace_compose hp ht
  exact ⟨m+k,ds,d,lt_of_lt_of_le hm (by simp),hd,hr⟩

theorem root_fresh_command (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) (hl : registers xs 8=0) :
    ∃k cs d,0<k ∧ Trace k cs (stateCode 1 xs) d ∧
      CommandRelation d (registers xs 0+1) (residual (registers xs 0))
        (ActualCommandStepGraph.stepValue (commandAtom (registers xs 0)) (commandState xs)) := by
  have fv : ValidStore (fetchNextEnd xs) := fetchDecodeEnd_valid _ (fetchFreshEnd_valid xs hv)
  have ef := fetchNextEnd_effect xs hv hl hc.2.1
  have fa : registers (fetchNextEnd xs) 3=decodeLeft (registers xs 0) := by rw [ef]; simp [PhysicalRegisters.write,hc.1]
  have fl : registers (fetchNextEnd xs) 8=decodeRight (registers xs 0) := by rw [ef]; simp [PhysicalRegisters.write]
  have fx : registers (fetchNextEnd xs) 6=0 := by rw [ef]; simp [PhysicalRegisters.write]
  have fy : registers (fetchNextEnd xs) 7=0 := by rw [ef]; simp [PhysicalRegisters.write]
  have fn : registers (fetchNextEnd xs) 0=registers xs 0+1 := by rw [ef]; simp [PhysicalRegisters.write]
  obtain ⟨m,ps,hm,hp⟩ := fetch_next_complete xs hv hl hc.2.1 hc.2.2
  obtain ⟨k,cs,d,hk,ht,hr⟩ := dispatch_command (fetchNextEnd xs) (registers xs 0) fv fa fl fx fy
  rw [fn,fetchNextEnd_commandState xs hv hl hc.2.1] at hr
  obtain ⟨ds,hd⟩ := trace_compose hp ht
  exact ⟨m+k,ds,d,lt_of_lt_of_le hm (by simp),hd,hr⟩
#print axioms root_positive_command
#print axioms root_fresh_command
end M6.Arithmetic.PA.InternalTrace.CodedSource

