module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceMPFinishStores
public import PA196.Source.MPSuccessPush
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
lemma mp_return_bound : Source.resolveAt PA196.Program.sites 3799=some (.jump (some 25)) := by
  rw [Program.resolve_tree]; decide +kernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma mp_return_step (xs : V) : stepValue (stateCode 3800 xs)=stateCode 26 xs := by
  have h := literal_step 3799 (by decide) _ mp_return_bound xs
  simpa only [instructionValue,destinationCode,Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using h
lemma mp_return_trace (xs : V) : Trace 1 ?[stateCode 3800 xs,stateCode 26 xs] (stateCode 3800 xs) (stateCode 26 xs) := by
  simpa only [mp_return_step] using trace_one (stateCode 3800 xs)
theorem actual_mp_success (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 3774 xs) (stateCode 26 (mpSuccessEnd xs)) := by
  have pushed : ∃n cs,0<n ∧ Trace n cs (stateCode 3774 xs) (stateCode 3793 (pushEnd xs)) :=
    push 3748 (by decide) PA196.Source.MPSuccessPush.bound xs hv hx hy
  obtain ⟨np,ps,hp,hP⟩ := pushed
  have pd : registers (pushEnd xs) 4=registers xs 4 := by rw [pushEnd_registers xs hv]; simp [PhysicalRegisters.write]
  have px : registers (pushEnd xs) 6=0 := by rw [pushEnd_registers xs hv]; simp [PhysicalRegisters.write,hx]
  have copied : ∃cs,Trace ((4*registers xs 4+1)+(3*registers xs 4+1)) cs
      (stateCode 3793 (pushEnd xs)) (stateCode 3800 (mpSuccessEnd xs)) := by
    exact copy_loop 3792 4 (by decide) (by decide) (by decide) PA196.Source.MPCopy.last_bound
      (registers xs 4) _ (pushEnd_valid xs hv) pd px
  obtain ⟨cs,hC⟩ := copied
  obtain ⟨ds,hd⟩ := trace_compose hP hC
  obtain ⟨es,he⟩ := trace_compose hd (mp_return_trace (mpSuccessEnd xs))
  exact ⟨np+((4*registers xs 4+1)+(3*registers xs 4+1))+1,es,by simp,he⟩
#print axioms mp_return_bound
#print axioms actual_mp_success
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

