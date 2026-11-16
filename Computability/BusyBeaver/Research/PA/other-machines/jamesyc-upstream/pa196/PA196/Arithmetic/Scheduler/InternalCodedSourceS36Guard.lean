module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceGuard
public import PA196.Arithmetic.Scheduler.InternalCodedSourceS36DrainPrefix
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
theorem actual_s36_guard (xs : V) (hv : ValidStore xs) :
    ∃ n cs,0<n ∧ Trace n cs (stateCode 3801 xs)
      (stateCode (if registers xs 6+registers xs 1+registers xs 5=1 then 0 else 12)
        (guardStore (s36DrainFinal xs) 0 0)) := by
  obtain ⟨n,cs,hn,hc⟩ := actual_s36_drain_prefix xs hv
  have hfirst : ValidStore (s36DrainFirst xs) := drainEnd_valid 1 6 _ xs hv
  have hsecond : ValidStore (s36DrainSecond xs) := drainTwoEnd_valid 5 1 6 _ _ hfirst
  have hfinal : ValidStore (s36DrainFinal xs) := drainEnd_valid 6 5 _ _ hsecond
  have hx : registers (s36DrainFinal xs) 6=0 := by
    rw [s36_drain_effect xs hv]
    simp [PhysicalRegisters.write]
  have hh : registers (s36DrainFinal xs) 5=registers xs 6+registers xs 1+registers xs 5 := by
    rw [s36_drain_effect xs hv]
    simp [PhysicalRegisters.write]
  have hg : guardStore (s36DrainFinal xs) (registers (s36DrainFinal xs) 5) 0=s36DrainFinal xs := by
    unfold guardStore
    have e : replace 5 (s36DrainFinal xs) (registers (s36DrainFinal xs) 5)=s36DrainFinal xs := replace_current (5:Fin 9) _ hfinal
    rw [e]
    have e2 : replace 6 (s36DrainFinal xs) (registers (s36DrainFinal xs) 6)=s36DrainFinal xs := replace_current (6:Fin 9) _ hfinal
    simpa only [hx] using e2
  obtain ⟨m,ds,hm,hd⟩ := actual_nip_guard (s36DrainFinal xs) (registers (s36DrainFinal xs) 5) hfinal
  rw [hg,hh] at hd
  obtain ⟨es,he⟩ := trace_compose hc hd
  exact ⟨n+m,es,lt_of_lt_of_le hn (by simp),he⟩
#print axioms actual_s36_guard
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

