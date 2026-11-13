module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceMPStores
public import PA196.Source.MPPush
public import PA196.Source.MPCopy
public import PA196.Source.MPCons
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
theorem actual_mp_prelude (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 3694 xs) (stateCode 3761 (mpAfterCons xs)) := by
  have field : ∃n cs,0<n ∧ Trace n cs (stateCode 3694 xs) (stateCode 3708 (mpAfterField xs)) := by
    exact unpair_relocated_store PA196.Source.MPField.relocation PA196.Source.MPField.bound (by decide) xs hv hx hy
  obtain ⟨nf,fs,hf,hF⟩ := field
  have fx : registers (mpAfterField xs) 6=0 := by rw [mpAfterField_registers xs hv]; simp [PhysicalRegisters.write]
  have fy : registers (mpAfterField xs) 7=0 := by rw [mpAfterField_registers xs hv]; simp [PhysicalRegisters.write]
  have pushed : ∃n cs,0<n ∧ Trace n cs (stateCode 3708 (mpAfterField xs)) (stateCode 3727 (mpAfterPush xs)) := by
    exact push 3682 (by decide) PA196.Source.MPPush.bound _ (mpAfterField_valid xs hv) fx fy
  obtain ⟨np,ps,hp,hP⟩ := pushed
  have pd : registers (mpAfterPush xs) 4=mpOffset xs := by
    rw [mpAfterPush_registers xs hv,mpAfterField_registers xs hv]; simp [PhysicalRegisters.write]
  have px : registers (mpAfterPush xs) 6=0 := by
    rw [mpAfterPush_registers xs hv,mpAfterField_registers xs hv]; simp [PhysicalRegisters.write]
  have copied : ∃cs,Trace ((4*mpOffset xs+1)+(3*mpOffset xs+1)) cs
      (stateCode 3727 (mpAfterPush xs)) (stateCode 3734 (mpAfterCopy xs)) := by
    exact copy_loop 3726 4 (by decide) (by decide) (by decide) PA196.Source.MPCopy.first_bound
      (mpOffset xs) _ (mpAfterPush_valid xs hv) pd px
  obtain ⟨cs,hC⟩ := copied
  have cx : registers (mpAfterCopy xs) 6=0 := by
    rw [mpAfterCopy_registers xs hv,mpAfterPush_registers xs hv,mpAfterField_registers xs hv]; simp [PhysicalRegisters.write]
  have cy : registers (mpAfterCopy xs) 7=0 := by
    rw [mpAfterCopy_registers xs hv,mpAfterPush_registers xs hv,mpAfterField_registers xs hv]; simp [PhysicalRegisters.write]
  have constructed : ∃n cs,0<n ∧ Trace n cs (stateCode 3734 (mpAfterCopy xs)) (stateCode 3761 (mpAfterCons xs)) := by
    exact cons_block 3713 (by decide) PA196.Source.MPCons.pop_bound PA196.Source.MPCons.pair_bound PA196.Source.MPCons.times_bound
      _ (mpAfterCopy_valid xs hv) cx cy
  obtain ⟨nk,ks,hk,hK⟩ := constructed
  obtain ⟨ds,hd⟩ := trace_compose hF hP
  obtain ⟨es,he⟩ := trace_compose hd hC
  obtain ⟨gs,hg⟩ := trace_compose he hK
  exact ⟨nf+np+((4*mpOffset xs+1)+(3*mpOffset xs+1))+nk,gs,lt_of_lt_of_le hf (by simp [add_assoc]),hg⟩
#print axioms actual_mp_prelude
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

