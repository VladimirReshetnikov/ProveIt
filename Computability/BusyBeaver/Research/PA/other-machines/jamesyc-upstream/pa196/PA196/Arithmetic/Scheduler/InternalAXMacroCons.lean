module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXMacroBasic
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma cons_store (s : Store V) (v : V) (vs : List V) (hstack : s.stack=v::vs) (bottom n : V) :
    CodedSource.consEnd (storeCode s bottom n)=storeCode {s with t:=im v s.t,stack:=vs} bottom n := by
  apply CodedSource.registers_ext (CodedSource.consEnd_valid _ (store_valid s bottom n)) (store_valid _ bottom n)
  rw [CodedSource.consEnd_registers _ (store_valid s bottom n),store_registers,store_registers]
  simp [registers,stackCode,hstack,im,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write,
    (SourceCantorInternal.decode_pairValue _ _).1,(SourceCantorInternal.decode_pairValue _ _).2]
lemma cons_realizes (offset : Nat) (hr : offset+47<3812)
    (hp : Source.UnpairPartial.Bound PA196.Program.sites (offset+20))
    (hq : Source.AXPair.Bound PA196.Program.sites offset)
    (hm : Source.AXTimes4.Bound PA196.Program.sites (offset+41)) :
    Realizes (V:=V) .cons (offset+20) (offset+47) := by
  intro s s' he bottom n
  cases hstack : s.stack with
  | nil => simp [exec,hstack] at he
  | cons v vs =>
    simp only [exec,hstack,Option.some.injEq] at he
    subst s'
    have hx : CodedSource.registers (storeCode s bottom n) 6=0 := by rw [store_registers];rfl
    have hy : CodedSource.registers (storeCode s bottom n) 7=0 := by rw [store_registers];rfl
    obtain ⟨k,cs,hk,hc⟩ := CodedSource.cons_block offset hr hp hq hm _ (store_valid s bottom n) hx hy
    refine ⟨k,cs,hk,?_⟩
    simpa only [config,Nat.add_assoc,Nat.reduceAdd,cons_store s v vs hstack bottom n] using hc
#print axioms cons_realizes
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX

