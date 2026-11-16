module
public import PA196.Arithmetic.Scheduler.SourceBindings
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairMain
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def unpairPartialEnd (r x y : Fin 9) (xs n : V) : V :=
  drainEnd y r (decodeRight n) (unpairDecodedStore r x y xs 0 n)
theorem unpair_partial (r x y : Fin 9) (base : Nat) (hrx : r≠x) (hry : r≠y) (hxy : x≠y)
    (hbound : base+10<3812) (hb : UnpairLoopBound r x y base)
    (b8 : Source.resolveAt PA196.Program.sites (base+8)=some (.dec y (some (base+11)) (some (base+9))))
    (b9 : Source.resolveAt PA196.Program.sites (base+9)=some (.inc r (some (base+10))))
    (b10 : Source.resolveAt PA196.Program.sites (base+10)=some (.jump (some (base+8))))
    (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs (stateCode ((base+1:Nat):V) (unpairStore r x y xs n 0 0))
      (stateCode ((base+11+1:Nat):V) (unpairPartialEnd r x y xs n)) := by
  obtain ⟨t,cs,ht,hc⟩ := unpair_main r x y base hrx hry hxy (by omega) hb n xs hv
  have hy : ValidStore (unpairDecodedStore r x y xs 0 n) := unpairStore_valid r x y xs 0 _ _ hv
  have hread : registers (unpairDecodedStore r x y xs 0 n) y=decodeRight n :=
    unpairStore_read_y r x y xs 0 _ _ hv
  obtain ⟨ds,hd⟩ := drain_loop (base+8) (base+9) (base+10) (base+11) y r hry.symm
    (by omega) (by omega) hbound b8 b9 b10 (decodeRight n) _ hy hread
  obtain ⟨es,he⟩ := trace_compose hc hd
  exact ⟨_,es,lt_of_lt_of_le ht (by simp),he⟩
theorem unpairPartialEnd_effect (r x y : Fin 9) (xs n : V) (hv : ValidStore xs)
    (hrx : r≠x) (hry : r≠y) (hxy : x≠y) :
    registers (unpairPartialEnd r x y xs n)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) r (decodeRight n)) x (decodeLeft n)) y 0 := by
  unfold unpairPartialEnd unpairDecodedStore
  rw [drainEnd_registers y r (decodeRight n) (unpairStore r x y xs 0 (decodeLeft n) (decodeRight n)) (unpairStore_valid r x y xs 0 (decodeLeft n) (decodeRight n) hv)]
  rw [unpairStore_registers r x y xs 0 _ _ hv]
  funext j
  by_cases hjr : j=r <;> by_cases hjx : j=x <;> by_cases hjy : j=y <;>
    simp_all [PhysicalRegisters.write]
theorem actual_unpair_partial (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs (stateCode 12 (unpairStore 2 6 7 xs n 0 0))
      (stateCode 23 (unpairPartialEnd 2 6 7 xs n)) := by
  apply unpair_partial 2 6 7 11 (by decide) (by decide) (by decide) (by decide)
    (unpairLoopBound_of_partial 11 SourceBindings.stack_partial)
  · exact SourceBindings.stack_partial ⟨8,by decide⟩
  · exact SourceBindings.stack_partial ⟨9,by decide⟩
  · exact SourceBindings.stack_partial ⟨10,by decide⟩
  · exact hv
#print axioms unpair_partial
#print axioms unpairPartialEnd_effect
#print axioms actual_unpair_partial
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

