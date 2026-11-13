module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXMacro
public import M6PA.Scheduler.InternalCodedSourceCons
public import M6PA.Scheduler.InternalCodedSourceCopyEffect
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def Realizes (op : Op) (start stop : Nat) : Prop :=
  ∀ s s' : Store V,exec op s=some s' → ∀ bottom n,
    ∃ k cs,0<k ∧ CodedSource.Trace k cs (config start s bottom n) (config stop s' bottom n)

lemma push_store (s : Store V) (bottom n : V) :
    CodedSource.pushEnd (storeCode s bottom n)=storeCode {s with t:=0,stack:=s.t::s.stack} bottom n := by
  apply CodedSource.registers_ext (CodedSource.pushEnd_valid _ (store_valid s bottom n)) (store_valid _ bottom n)
  rw [CodedSource.pushEnd_registers _ (store_valid s bottom n),store_registers,store_registers]
  simp [registers,stackCode,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma push_realizes (offset : Nat) (hr : offset+44<3947)
    (hb : Source.AXPushParam.Bound Source.exactSites offset) :
    Realizes (V:=V) .push (offset+25) (offset+44) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  have hx : CodedSource.registers (storeCode s bottom n) 6=0 := by rw [store_registers];rfl
  have hy : CodedSource.registers (storeCode s bottom n) 7=0 := by rw [store_registers];rfl
  obtain ⟨k,cs,hk,hc⟩ := CodedSource.push offset hr hb _ (store_valid s bottom n) hx hy
  refine ⟨k,cs,hk,?_⟩
  simpa only [config,Nat.add_assoc,Nat.reduceAdd,push_store] using hc

lemma copy_store (r : Fin 9) (h1 : r≠1) (h6 : r≠6) (s : Store V) (v bottom n : V)
    (hr : registers s bottom n r=v) :
    CodedSource.copyEnd r v (storeCode s bottom n)=storeCode {s with t:=s.t+v} bottom n := by
  have hx : CodedSource.registers (storeCode s bottom n) 6=0 := by rw [store_registers];rfl
  apply CodedSource.registers_ext (CodedSource.copyEnd_valid r v _ (store_valid s bottom n)) (store_valid _ bottom n)
  rw [CodedSource.copyEnd_effect r v _ (store_valid s bottom n) h1 h6 (by rwa [store_registers]) hx,
    store_registers,store_registers]
  simp [registers,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma copy_trace (base : Nat) (r : Fin 9) (h1 : r≠1) (h6 : r≠6) (hrange : base+7<3947)
    (hb : Source.CopyToT.Bound Source.exactSites r base) (s : Store V) (v bottom n : V)
    (hr : registers s bottom n r=v) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs (config base s bottom n) (config (base+7) {s with t:=s.t+v} bottom n) := by
  have hx : CodedSource.registers (storeCode s bottom n) 6=0 := by rw [store_registers];rfl
  obtain ⟨cs,hc⟩ := CodedSource.copy_loop base r h1 h6 (by omega) hb v _ (store_valid s bottom n) (by rwa [store_registers]) hx
  refine ⟨(4*v+1)+(3*v+1),cs,lt_of_lt_of_le (show (0:V)<4*v+1 by simp) (by simp),?_⟩
  simpa only [config,Nat.add_assoc,Nat.reduceAdd,copy_store r h1 h6 s v bottom n hr] using hc

lemma copyA_realizes (base : Nat) (hrange : base+7<3947)
    (hb : Source.CopyToT.Bound Source.exactSites 3 base) : Realizes (V:=V) .copyA base (base+7) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  exact copy_trace base 3 (by decide) (by decide) hrange hb s s.a bottom n rfl
lemma copyD_realizes (base : Nat) (hrange : base+7<3947)
    (hb : Source.CopyToT.Bound Source.exactSites 4 base) : Realizes (V:=V) .copyD base (base+7) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  exact copy_trace base 4 (by decide) (by decide) hrange hb s s.d bottom n rfl
lemma copyH_realizes (base : Nat) (hrange : base+7<3947)
    (hb : Source.CopyToT.Bound Source.exactSites 5 base) : Realizes (V:=V) .copyH base (base+7) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  exact copy_trace base 5 (by decide) (by decide) hrange hb s s.h bottom n rfl

lemma inc_store (s : Store V) (bottom n : V) :
    CodedSource.replace 1 (storeCode s bottom n) (s.t+1)=storeCode {s with t:=s.t+1} bottom n := by
  apply CodedSource.registers_ext (xs:=CodedSource.replace 1 (storeCode s bottom n) (s.t+1))
    (CodedSource.replace_valid _ _ (store_valid s bottom n) 1) (store_valid _ bottom n)
  have hr : CodedSource.registers (CodedSource.replace 1 (storeCode s bottom n) (s.t+1))=
      PhysicalRegisters.write (CodedSource.registers (storeCode s bottom n)) 1 (s.t+1) :=
    CodedSource.registers_replace _ _ (store_valid s bottom n) 1
  rw [hr,store_registers,store_registers]
  simp [registers,funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma inc_realizes (base : Nat) (hrange : base+1<3947)
    (hb : Source.resolveAt Source.exactSites base=some (.inc 1 (some (base+1)))) :
    Realizes (V:=V) .incT base (base+1) := by
  intro s s' he bottom n
  simp only [exec,Option.some.injEq] at he
  subst s'
  have hs : CodedSource.stepValue (config base s bottom n)=config (base+1) {s with t:=s.t+1} bottom n := by
    rw [config,CodedSource.literal_step base (by omega) _ hb]
    have ht : CodedSource.registers (storeCode s bottom n) 1=s.t := by rw [store_registers];rfl
    change CodedSource.stateCode ((base+1+1:Nat):V)
      (CodedSource.replace 1 (storeCode s bottom n) (CodedSource.registers (storeCode s bottom n) 1+1)) = _
    rw [ht,inc_store]
    rfl
  refine ⟨1,?[config base s bottom n,config (base+1) {s with t:=s.t+1} bottom n],by simp,?_⟩
  simpa only [hs] using CodedSource.trace_one (config base s bottom n)
#print axioms push_realizes
#print axioms copyA_realizes
#print axioms copyD_realizes
#print axioms copyH_realizes
#print axioms inc_realizes
end M6.Arithmetic.PA.InternalTrace.ModelAX

