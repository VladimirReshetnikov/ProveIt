module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6.Source.AXMacroRead
public import M6PA.Scheduler.InternalAXMacroCons
public import M6PA.Scheduler.InternalCodedSourceUnpairApply
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma readerH_store (s : Store V) (bottom n : V) :
    CodedSource.unpairFullEnd 8 6 7 5 (storeCode s bottom n) s.l=
      storeCode {s with h:=s.h+SourceCantorInternal.decodeLeft s.l,l:=SourceCantorInternal.decodeRight s.l} bottom n := by
  apply CodedSource.registers_ext (CodedSource.unpairFullEnd_valid _ _ _ _ _ _ (store_valid s bottom n)) (store_valid _ bottom n)
  rw [CodedSource.unpairFullEnd_effect 8 6 7 5 _ _ (store_valid s bottom n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),store_registers,store_registers]
  simp [registers,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma readH_realizes (base : Nat) (hr : base+14<3947)
    (hb : (Source.AXMacro.readerH base).Bound) : Realizes (V:=V) .readH base (base+14) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  have hx : CodedSource.registers (storeCode s bottom n) ((Source.AXMacro.readerH base).rename 6)=0 := by
    rw [store_registers];rfl
  have hy : CodedSource.registers (storeCode s bottom n) ((Source.AXMacro.readerH base).rename 7)=0 := by
    rw [store_registers];rfl
  obtain ⟨k,cs,hk,hc⟩ := CodedSource.unpair_relocated_store (Source.AXMacro.readerH base) hb
    (by change base+13<3947;omega) _ (store_valid s bottom n) hx hy
  refine ⟨k,cs,hk,?_⟩
  have he : (Source.AXMacro.readerH base).rename 2=8 := rfl
  have hx' : (Source.AXMacro.readerH base).rename 6=6 := rfl
  have hy' : (Source.AXMacro.readerH base).rename 7=7 := rfl
  have hh : (Source.AXMacro.readerH base).rename 5=5 := rfl
  rw [he,hx',hy',hh,store_registers] at hc
  change CodedSource.Trace k cs (CodedSource.stateCode ((base+1:Nat):V) (storeCode s bottom n))
    (CodedSource.stateCode ((base+14+1:Nat):V) (CodedSource.unpairFullEnd 8 6 7 5 (storeCode s bottom n) s.l)) at hc
  simpa only [config,readerH_store] using hc

lemma readerD_store (s : Store V) (bottom n : V) :
    CodedSource.unpairFullEnd 8 6 7 4 (storeCode s bottom n) s.l=
      storeCode {s with d:=s.d+SourceCantorInternal.decodeLeft s.l,l:=SourceCantorInternal.decodeRight s.l} bottom n := by
  apply CodedSource.registers_ext (CodedSource.unpairFullEnd_valid _ _ _ _ _ _ (store_valid s bottom n)) (store_valid _ bottom n)
  rw [CodedSource.unpairFullEnd_effect 8 6 7 4 _ _ (store_valid s bottom n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),store_registers,store_registers]
  simp [registers,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma readD_realizes (base : Nat) (hr : base+14<3947)
    (hb : (Source.AXMacro.readerD base).Bound) : Realizes (V:=V) .readD base (base+14) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  have hx : CodedSource.registers (storeCode s bottom n) ((Source.AXMacro.readerD base).rename 6)=0 := by
    rw [store_registers];rfl
  have hy : CodedSource.registers (storeCode s bottom n) ((Source.AXMacro.readerD base).rename 7)=0 := by
    rw [store_registers];rfl
  obtain ⟨k,cs,hk,hc⟩ := CodedSource.unpair_relocated_store (Source.AXMacro.readerD base) hb
    (by change base+13<3947;omega) _ (store_valid s bottom n) hx hy
  refine ⟨k,cs,hk,?_⟩
  have he : (Source.AXMacro.readerD base).rename 2=8 := rfl
  have hx' : (Source.AXMacro.readerD base).rename 6=6 := rfl
  have hy' : (Source.AXMacro.readerD base).rename 7=7 := rfl
  have hh : (Source.AXMacro.readerD base).rename 5=4 := rfl
  rw [he,hx',hy',hh,store_registers] at hc
  change CodedSource.Trace k cs (CodedSource.stateCode ((base+1:Nat):V) (storeCode s bottom n))
    (CodedSource.stateCode ((base+14+1:Nat):V) (CodedSource.unpairFullEnd 8 6 7 4 (storeCode s bottom n) s.l)) at hc
  simpa only [config,readerD_store] using hc
#print axioms readH_realizes
#print axioms readD_realizes
end M6.Arithmetic.PA.InternalTrace.ModelAX

