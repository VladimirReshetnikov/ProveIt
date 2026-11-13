module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairRelocation
public import PA196.Arithmetic.Scheduler.InternalCodedSourceS36
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma unpairPartialEnd_valid (r x y : Fin 9) (xs n : V) (hv : ValidStore xs) :
    ValidStore (unpairPartialEnd r x y xs n) :=
  drainEnd_valid y r _ _ (unpairStore_valid r x y xs 0 _ _ hv)
lemma unpairFullEnd_valid (r x y h : Fin 9) (xs n : V) (hv : ValidStore xs) :
    ValidStore (unpairFullEnd r x y h xs n) :=
  drainEnd_valid x h _ _ (unpairPartialEnd_valid r x y xs n hv)
theorem unpair_partial_store (base : Nat) (hbound : base+10<3812)
    (hb : Source.UnpairPartial.Bound PA196.Program.sites base) (xs : V) (hv : ValidStore xs)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃t cs,0<t ∧ Trace t cs (stateCode ((base+1:Nat):V) xs)
      (stateCode ((base+11+1:Nat):V) (unpairPartialEnd 2 6 7 xs (registers xs 2))) := by
  have h := unpair_partial 2 6 7 base (by decide) (by decide) (by decide) hbound
    (unpairLoopBound_of_partial base hb) (by exact hb ⟨8,by decide⟩) (by exact hb ⟨9,by decide⟩) (by exact hb ⟨10,by decide⟩)
    (registers xs 2) xs hv
  simpa only [unpairStore_current 2 6 7 xs hv hx hy] using h
theorem unpair_relocated_store (p : Source.UnpairRelocation) (hb : PA196.Source.Readers.Bound PA196.Program.sites p) (hbound : p.base+13<3812)
    (xs : V) (hv : ValidStore xs) (hx : registers xs (p.rename 6)=0) (hy : registers xs (p.rename 7)=0) :
    ∃t cs,0<t ∧ Trace t cs (stateCode ((p.base+1:Nat):V) xs)
      (stateCode ((p.exitPort+1:Nat):V)
        (unpairFullEnd (p.rename 2) (p.rename 6) (p.rename 7) (p.rename 5) xs (registers xs (p.rename 2)))) := by
  have h := unpair_relocated p hb hbound (registers xs (p.rename 2)) xs hv
  simpa only [unpairStore_current (p.rename 2) (p.rename 6) (p.rename 7) xs hv hx hy] using h
#print axioms unpair_partial_store
#print axioms unpair_relocated_store
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

