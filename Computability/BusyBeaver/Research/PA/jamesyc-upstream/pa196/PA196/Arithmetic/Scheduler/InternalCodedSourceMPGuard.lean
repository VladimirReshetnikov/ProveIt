module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCompareBindings
public import PA196.Arithmetic.Scheduler.InternalCodedSourceS36
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma guardStore_current (xs : V) (hv : ValidStore xs) :
    guardStore xs (registers xs 5) (registers xs 6)=xs := by
  unfold guardStore
  have e5 : replace 5 xs (registers xs 5)=xs := replace_current (5:Fin 9) xs hv
  have e6 : replace 6 xs (registers xs 6)=xs := replace_current (6:Fin 9) xs hv
  rw [e5,e6]
noncomputable def mpGuardEnd (xs : V) : V := guardStore (drainEnd 1 6 (registers xs 1) xs) 0 0
theorem actual_mp_guard (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) :
    ∃t cs,0<t ∧ Trace t cs (stateCode 3761 xs)
      (stateCode (if registers xs 1=registers xs 5 then 3774 else 3800) (mpGuardEnd xs)) := by
  have b0 : Source.resolveAt PA196.Program.sites 3760=some (.dec 1 (some 3763) (some 3761)) := by (simp only [Program.resolve_tree]; decide +kernel)
  have b1 : Source.resolveAt PA196.Program.sites 3761=some (.inc 6 (some 3762)) := by (simp only [Program.resolve_tree]; decide +kernel)
  have b2 : Source.resolveAt PA196.Program.sites 3762=some (.jump (some 3760)) := by (simp only [Program.resolve_tree]; decide +kernel)
  obtain ⟨cs,hc⟩ := drain_loop 3760 3761 3762 3763 1 6 (by decide) (by decide) (by decide) (by decide)
    b0 b1 b2 (registers xs 1) xs hv rfl
  let ys := drainEnd 1 6 (registers xs 1) xs
  have hy : ValidStore ys := drainEnd_valid 1 6 _ xs hv
  have hY : registers ys 5=registers xs 5 := by
    rw [drainEnd_registers 1 6 (registers xs 1) xs hv]
    simp [PhysicalRegisters.write]
  have xY : registers ys 6=registers xs 1 := by
    rw [drainEnd_registers 1 6 (registers xs 1) xs hv]
    simp [PhysicalRegisters.write,hx]
  obtain ⟨n,ds,hn,hd⟩ := compare_loop 3763 3773 3799 (by decide) mp_compare_bound (registers ys 5) (registers ys 6) ys hy
  rw [guardStore_current ys hy,hY,xY] at hd
  obtain ⟨es,he⟩ := trace_compose hc hd
  refine ⟨3*registers xs 1+1+n,es,by simp,?_⟩
  simpa only [Nat.reduceAdd,Nat.cast_ofNat,mpGuardEnd,ys,eq_comm] using he
lemma mpGuardEnd_effect (xs : V) (hv : ValidStore xs) :
    registers (mpGuardEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 1 0) 5 0) 6 0 := by
  unfold mpGuardEnd
  rw [guardStore_registers _ 0 0 (drainEnd_valid 1 6 _ xs hv),drainEnd_registers 1 6 (registers xs 1) xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h5:j=5 <;> by_cases h6:j=6 <;> simp_all [PhysicalRegisters.write]
#print axioms actual_mp_guard
#print axioms mpGuardEnd_effect
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

