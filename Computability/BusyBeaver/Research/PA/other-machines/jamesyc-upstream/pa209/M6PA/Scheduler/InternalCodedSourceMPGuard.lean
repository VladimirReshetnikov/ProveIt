module
import all M6.Source.MPGuardSteps
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCompareBindings
public import M6PA.Scheduler.InternalCodedSourceS36
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma guardStore_current (xs : V) (hv : ValidStore xs) :
    guardStore xs (registers xs 5) (registers xs 6)=xs := by
  unfold guardStore
  have e5 : replace 5 xs (registers xs 5)=xs := replace_current (5:Fin 9) xs hv
  have e6 : replace 6 xs (registers xs 6)=xs := replace_current (6:Fin 9) xs hv
  rw [e5,e6]
noncomputable def mpGuardEnd (xs : V) : V := guardStore (drainEnd 1 6 (registers xs 1) xs) 0 0
theorem actual_mp_guard (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) :
    ∃t cs,0<t ∧ Trace t cs (stateCode 3872 xs)
      (stateCode (if registers xs 1=registers xs 5 then 3885 else 3911) (mpGuardEnd xs)) := by
  have b0 : Source.resolveAt Source.exactSites 3871=some (.dec 1 (some 3874) (some 3872)) := by exact_retained_mp_row 3871
  have b1 : Source.resolveAt Source.exactSites 3872=some (.inc 6 (some 3873)) := by exact_retained_mp_row 3872
  have b2 : Source.resolveAt Source.exactSites 3873=some (.jump (some 3871)) := by exact_retained_mp_row 3873
  obtain ⟨cs,hc⟩ := drain_loop 3871 3872 3873 3874 1 6 (by decide) (by decide) (by decide) (by decide)
    b0 b1 b2 (registers xs 1) xs hv rfl
  let ys := drainEnd 1 6 (registers xs 1) xs
  have hy : ValidStore ys := drainEnd_valid 1 6 _ xs hv
  have hY : registers ys 5=registers xs 5 := by
    rw [drainEnd_registers 1 6 (registers xs 1) xs hv]
    simp [PhysicalRegisters.write]
  have xY : registers ys 6=registers xs 1 := by
    rw [drainEnd_registers 1 6 (registers xs 1) xs hv]
    simp [PhysicalRegisters.write,hx]
  obtain ⟨n,ds,hn,hd⟩ := compare_loop 3874 3884 3910 (by decide) mp_compare_bound (registers ys 5) (registers ys 6) ys hy
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
end M6.Arithmetic.PA.InternalTrace.CodedSource

