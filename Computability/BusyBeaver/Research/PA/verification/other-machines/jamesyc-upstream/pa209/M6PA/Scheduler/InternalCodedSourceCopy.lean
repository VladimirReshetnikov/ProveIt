module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceS36DrainPrefix
public import M6.Source.CopyToT
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def copyEnd (r : Fin 9) (n xs : V) : V :=
  drainEnd 6 r n (drainTwoEnd r 1 6 n xs)
theorem copy_loop (base : Nat) (r : Fin 9) (h1 : r≠1) (h6 : r≠6)
    (hbound : base+6<3947) (hb : Source.CopyToT.Bound Source.exactSites r base)
    (n xs : V) (hv : ValidStore xs) (hr : registers xs r=n) (hx : registers xs 6=0) :
    ∃ cs, Trace ((4*n+1)+(3*n+1)) cs (stateCode ((base+1:Nat):V) xs)
      (stateCode ((base+8:Nat):V) (copyEnd r n xs)) := by
  have first : ∃ cs,Trace (4*n+1) cs (stateCode ((base+1:Nat):V) xs)
      (stateCode ((base+4+1:Nat):V) (drainTwoEnd r 1 6 n xs)) := by
    apply drain_two_loop base (base+1) (base+2) (base+3) (base+4) r 1 6 h1 h6 (by decide)
      (by omega) (by omega) (by omega) (by omega)
    · simpa only [Source.CopyToT.expected,Nat.add_zero] using hb ⟨0,by decide⟩
    · exact hb ⟨1,by decide⟩
    · exact hb ⟨2,by decide⟩
    · exact hb ⟨3,by decide⟩
    · exact hv
    · exact hr
  have hy : ValidStore (drainTwoEnd r 1 6 n xs) := drainTwoEnd_valid r 1 6 n xs hv
  have hread : registers (drainTwoEnd r 1 6 n xs) 6=n := by
    rw [drainTwoEnd_registers r 1 6 n xs hv]
    simp [PhysicalRegisters.write,hx]
  have second : ∃ ds,Trace (3*n+1) ds (stateCode ((base+4+1:Nat):V) (drainTwoEnd r 1 6 n xs))
      (stateCode ((base+7+1:Nat):V) (copyEnd r n xs)) := by
    apply drain_loop (base+4) (base+5) (base+6) (base+7) 6 r h6.symm
      (by omega) (by omega) hbound
    · exact hb ⟨4,by decide⟩
    · exact hb ⟨5,by decide⟩
    · exact hb ⟨6,by decide⟩
    · exact hy
    · exact hread
  obtain ⟨cs,hc⟩ := first
  obtain ⟨ds,hd⟩ := second
  simpa only [Nat.add_assoc] using trace_compose hc hd

theorem copyEnd_effect (r : Fin 9) (n xs : V) (hv : ValidStore xs)
    (h1 : r≠1) (h6 : r≠6) (hr : registers xs r=n) (hx : registers xs 6=0) :
    registers (copyEnd r n xs)=PhysicalRegisters.write (registers xs) 1 (registers xs 1+n) := by
  unfold copyEnd
  rw [drainEnd_registers 6 r n _ (drainTwoEnd_valid r 1 6 n xs hv),drainTwoEnd_registers r 1 6 n xs hv]
  funext j
  by_cases hj : j=r <;> by_cases hj1 : j=1 <;> by_cases hj6 : j=6 <;>
    simp_all [PhysicalRegisters.write]
#print axioms copy_loop
#print axioms copyEnd_effect
end M6.Arithmetic.PA.InternalTrace.CodedSource

