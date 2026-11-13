module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXMacroBasic
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma cons_store (s : Store V) (v : V) (vs : List V) (hstack : s.stack=v::vs) (bottom n : V) :
    CodedSource.consEnd (storeCode s bottom n)=storeCode {s with t:=im v s.t,stack:=vs} bottom n := by
  apply CodedSource.registers_ext (CodedSource.consEnd_valid _ (store_valid s bottom n)) (store_valid _ bottom n)
  rw [CodedSource.consEnd_registers _ (store_valid s bottom n),store_registers,store_registers]
  simp [registers,stackCode,hstack,im,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write,
    (SourceCantorInternal.decode_pairValue _ _).1,(SourceCantorInternal.decode_pairValue _ _).2]
lemma cons_realizes (offset : Nat) (hr : offset+47<3947)
    (hp : Source.UnpairPartial.Bound Source.exactSites (offset+20))
    (hq : Source.AXPair.Bound Source.exactSites offset)
    (hm : Source.AXTimes4.Bound Source.exactSites (offset+41)) :
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
end M6.Arithmetic.PA.InternalTrace.ModelAX

