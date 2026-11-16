module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrainTwo
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem actual_s36_drain_H (n xs : V) (hv : ValidStore xs) (ht : registers xs 5=n) :
    ∃ cs, Trace (4*n+1) cs (stateCode 3804 xs) (stateCode 3808 (drainTwoEnd 5 1 6 n xs)) := by
  apply drain_two_loop 3803 3804 3805 3806 3807 5 1 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · exact PA196.Source.s36_resolved_at ⟨3,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨4,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨5,by decide⟩
  · exact PA196.Source.s36_resolved_at ⟨6,by decide⟩
  · exact hv
  · exact ht

theorem drainEnd_valid (r s : Fin 9) (n xs : V) (hv : ValidStore xs) : ValidStore (drainEnd r s n xs) :=
  replace_valid _ _ (replace_valid xs 0 hv r) s
theorem drainTwoEnd_valid (r s u : Fin 9) (n xs : V) (hv : ValidStore xs) : ValidStore (drainTwoEnd r s u n xs) :=
  replace_valid _ _ (drainEnd_valid r s n xs hv) u

theorem drainEnd_registers (r s : Fin 9) (n xs : V) (hv : ValidStore xs) :
    registers (drainEnd r s n xs)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) r 0) s (registers xs s+n) := by
  unfold drainEnd
  rw [registers_replace _ _ (replace_valid xs 0 hv r) s,registers_replace xs 0 hv r]
theorem drainTwoEnd_registers (r s u : Fin 9) (n xs : V) (hv : ValidStore xs) :
    registers (drainTwoEnd r s u n xs)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) r 0) s (registers xs s+n)) u (registers xs u+n) := by
  unfold drainTwoEnd
  rw [registers_replace _ _ (drainEnd_valid r s n xs hv) u,drainEnd_registers r s n xs hv]

noncomputable def s36DrainFirst (xs : V) : V := drainEnd 1 6 (registers xs 1) xs
noncomputable def s36DrainSecond (xs : V) : V :=
  drainTwoEnd 5 1 6 (registers (s36DrainFirst xs) 5) (s36DrainFirst xs)
noncomputable def s36DrainFinal (xs : V) : V :=
  drainEnd 6 5 (registers (s36DrainSecond xs) 6) (s36DrainSecond xs)

theorem actual_s36_drain_prefix (xs : V) (hv : ValidStore xs) :
    ∃ n cs, 0<n ∧ Trace n cs (stateCode 3801 xs) (stateCode 3811 (s36DrainFinal xs)) := by
  have h1 := drainEnd_valid 1 6 (registers xs 1) xs hv
  have h2 := drainTwoEnd_valid 5 1 6 (registers (s36DrainFirst xs) 5) (s36DrainFirst xs) h1
  obtain ⟨as,ha⟩ := actual_s36_drain_T (registers xs 1) xs hv rfl
  obtain ⟨bs,hb⟩ := actual_s36_drain_H (registers (s36DrainFirst xs) 5) (s36DrainFirst xs) h1 rfl
  obtain ⟨cs,hc⟩ := actual_s36_drain_X (registers (s36DrainSecond xs) 6) (s36DrainSecond xs) h2 rfl
  obtain ⟨ds,hd⟩ := trace_compose ha hb
  obtain ⟨es,he⟩ := trace_compose hd hc
  refine ⟨_,es,?_,he⟩
  exact lt_of_lt_of_le (show (0:V)<3*registers xs 1+1 by simp) (by simp)

/-- Full logical register effect of all ten actual pre-guard leaves. -/
theorem s36_drain_effect (xs : V) (hv : ValidStore xs) :
    registers (s36DrainFinal xs)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs)
        1 (registers xs 5)) 5 (registers xs 6+registers xs 1+registers xs 5)) 6 0 := by
  have h1 := drainEnd_valid 1 6 (registers xs 1) xs hv
  have h2 := drainTwoEnd_valid 5 1 6 (registers (s36DrainFirst xs) 5) (s36DrainFirst xs) h1
  have e1 := drainEnd_registers 1 6 (registers xs 1) xs hv
  change registers (s36DrainFirst xs)=_ at e1
  have e2 := drainTwoEnd_registers 5 1 6 (registers (s36DrainFirst xs) 5) (s36DrainFirst xs) h1
  change registers (s36DrainSecond xs)=_ at e2
  rw [s36DrainFinal,drainEnd_registers 6 5 (registers (s36DrainSecond xs) 6) (s36DrainSecond xs) h2]
  simp only [e2,e1]
  funext r
  by_cases hr1 : r=1 <;> by_cases hr5 : r=5 <;> by_cases hr6 : r=6 <;>
    simp_all [PhysicalRegisters.write,add_assoc]
#print axioms actual_s36_drain_H
#print axioms actual_s36_drain_prefix
#print axioms s36_drain_effect
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

