module
public import PA196.Arithmetic.Scheduler.SourceBindings
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairPartial
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrainOption
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def unpairFullEnd (r x y h : Fin 9) (xs n : V) : V :=
  drainEnd x h (decodeLeft n) (unpairPartialEnd r x y xs n)
theorem unpair_full_tail (r x y h : Fin 9) (base : Nat) (exit : Option Nat)
    (hrx : r≠x) (hry : r≠y) (hxy : x≠y) (hxh : x≠h)
    (hbound : base+13<3812)
    (b11 : Source.resolveAt PA196.Program.sites (base+11)=some (.dec x exit (some (base+12))))
    (b12 : Source.resolveAt PA196.Program.sites (base+12)=some (.inc h (some (base+13))))
    (b13 : Source.resolveAt PA196.Program.sites (base+13)=some (.jump (some (base+11))))
    (n xs : V) (hv : ValidStore xs) :
    ∃ cs,Trace (3*decodeLeft n+1) cs (stateCode ((base+11+1:Nat):V) (unpairPartialEnd r x y xs n))
      (stateCode ((destinationCode exit:Nat):V) (unpairFullEnd r x y h xs n)) := by
  have hp : ValidStore (unpairPartialEnd r x y xs n) :=
    drainEnd_valid y r _ _ (unpairStore_valid r x y xs 0 _ _ hv)
  have hx : registers (unpairPartialEnd r x y xs n) x=decodeLeft n := by
    rw [unpairPartialEnd_effect r x y xs n hv hrx hry hxy]
    simp [PhysicalRegisters.write,hxy]
  exact drain_loop_option (base+11) (base+12) (base+13) exit x h hxh
    (by omega) (by omega) hbound b11 b12 b13 (decodeLeft n) _ hp hx

theorem unpairFullEnd_effect (r x y h : Fin 9) (xs n : V) (hv : ValidStore xs)
    (hrx : r≠x) (hry : r≠y) (hxy : x≠y) (hhr : h≠r) (hhx : h≠x) (hhy : h≠y) :
    registers (unpairFullEnd r x y h xs n)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
        (PhysicalRegisters.write (registers xs) r (decodeRight n)) x 0) y 0) h (registers xs h+decodeLeft n) := by
  unfold unpairFullEnd
  have hp : ValidStore (unpairPartialEnd r x y xs n) := drainEnd_valid y r _ _ (unpairStore_valid r x y xs 0 _ _ hv)
  rw [drainEnd_registers x h (decodeLeft n) (unpairPartialEnd r x y xs n) hp,
    unpairPartialEnd_effect r x y xs n hv hrx hry hxy]
  funext j
  by_cases hjr : j=r <;> by_cases hjx : j=x <;> by_cases hjy : j=y <;> by_cases hjh : j=h <;>
    simp_all [PhysicalRegisters.write]
theorem actual_unpair_full (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs (stateCode 12 (unpairStore 2 6 7 xs n 0 0))
      (stateCode 26 (unpairFullEnd 2 6 7 5 xs n)) := by
  obtain ⟨t,cs,ht,hc⟩ := actual_unpair_partial n xs hv
  have tail : ∃ ds,Trace (3*decodeLeft n+1) ds (stateCode 23 (unpairPartialEnd 2 6 7 xs n))
      (stateCode 26 (unpairFullEnd 2 6 7 5 xs n)) := by
    have h := unpair_full_tail 2 6 7 5 11 (some 25) (by decide) (by decide) (by decide) (by decide) (by decide)
      SourceBindings.stack_last11 SourceBindings.stack_last12
      SourceBindings.stack_last13 n xs hv
    simpa only [destinationCode,Nat.cast_one,Nat.reduceAdd,Nat.cast_ofNat] using h
  obtain ⟨ds,hd⟩ := tail
  obtain ⟨es,he⟩ := trace_compose hc hd
  exact ⟨_,es,lt_of_lt_of_le ht (by simp),he⟩
#print axioms unpairFullEnd_effect
#print axioms actual_unpair_full
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

