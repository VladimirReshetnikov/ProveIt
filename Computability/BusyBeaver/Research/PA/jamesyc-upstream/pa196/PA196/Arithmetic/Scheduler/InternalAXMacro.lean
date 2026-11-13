module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourcePush
public import M6PA.Scheduler.SourceCantorInjectiveInternal
public import PA196.Source.AXSymbolic
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
abbrev Op := Source.AXMacro.Op
structure Store (V : Type*) where
  t : V
  a : V
  d : V
  h : V
  l : V
  stack : List V
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def im (a b : V) : V := 4*SourceCantorInternal.pairValue a b
noncomputable def stackCode : List V → V → V
  | [], bottom => bottom
  | x::xs, bottom => SourceCantorInternal.pairValue x (stackCode xs bottom)
noncomputable def exec : Op → Store V → Option (Store V)
  | .push, s => some {s with t:=0,stack:=s.t::s.stack}
  | .cons, s => match s.stack with
    | [] => none
    | v::vs => some {s with t:=im v s.t,stack:=vs}
  | .copyA,s => some {s with t:=s.t+s.a}
  | .copyD,s => some {s with t:=s.t+s.d}
  | .copyH,s => some {s with t:=s.t+s.h}
  | .incT,s => some {s with t:=s.t+1}
  | .readH,s => some {s with h:=s.h+SourceCantorInternal.decodeLeft s.l,l:=SourceCantorInternal.decodeRight s.l}
  | .readD,s => some {s with d:=s.d+SourceCantorInternal.decodeLeft s.l,l:=SourceCantorInternal.decodeRight s.l}
noncomputable def run : List Op → Store V → Option (Store V)
  | [],s => some s
  | op::ops,s => (exec op s).bind (run ops)
noncomputable def storeCode (s : Store V) (bottom n : V) : V :=
  ?[n,s.t,stackCode s.stack bottom,s.a,s.d,s.h,0,0,s.l]
noncomputable def config (pc : Nat) (s : Store V) (bottom n : V) : V :=
  CodedSource.stateCode ((pc+1:Nat):V) (storeCode s bottom n)
noncomputable def registers (s : Store V) (bottom n : V) : Fin 9 → V :=
  ![n,s.t,stackCode s.stack bottom,s.a,s.d,s.h,0,0,s.l]
lemma store_valid (s : Store V) (bottom n : V) : CodedSource.ValidStore (storeCode s bottom n) := by
  simp [CodedSource.ValidStore,storeCode]
  norm_num
lemma store_registers (s : Store V) (bottom n : V) :
    CodedSource.registers (storeCode s bottom n)=registers s bottom n := by
  simp [funext_iff,Fin.forall_fin_succ,CodedSource.registers,registers,storeCode]

noncomputable def eval (v : Fin 6 → V) : Source.AXSymbolic.Expr → V
  | .zero => 0
  | .atom i => v i
  | .succ x => eval v x+1
  | .add x y => eval v x+eval v y
  | .im x y => im (eval v x) (eval v y)
lemma eval_plus (v : Fin 6 → V) (x y : Source.AXSymbolic.Expr) :
    eval v (Source.AXSymbolic.plus x y)=eval v x+eval v y := by
  cases x <;> cases y <;> simp [Source.AXSymbolic.plus,eval]
noncomputable def materialize (v : Fin 6 → V) (tail : V) (s : Source.AXSymbolic.Store) : Store V :=
  ⟨eval v s.t,eval v s.a,eval v s.d,eval v s.h,stackCode (s.fields.map (eval v)) tail,s.stack.map (eval v)⟩
lemma exec_symbolic (op : Op) (s s' : Source.AXSymbolic.Store)
    (he : Source.AXSymbolic.exec op s=some s') (v : Fin 6 → V) (tail : V) :
    exec op (materialize v tail s)=some (materialize v tail s') := by
  cases op <;> cases s with
  | mk t a d h fields stack =>
    cases fields <;> cases stack <;>
      simp only [Source.AXSymbolic.exec,Option.some.injEq] at he <;> cases he <;>
      simp_all [materialize,exec,eval,eval_plus,stackCode,
        (SourceCantorInternal.decode_pairValue _ _).1,(SourceCantorInternal.decode_pairValue _ _).2]
lemma run_symbolic (ops : List Op) (s s' : Source.AXSymbolic.Store)
    (he : Source.AXSymbolic.run ops s=some s') (v : Fin 6 → V) (tail : V) :
    run ops (materialize v tail s)=some (materialize v tail s') := by
  induction ops generalizing s with
  | nil =>
    simp only [Source.AXSymbolic.run,Option.some.injEq] at he
    subst s'
    rfl
  | cons op ops ih =>
    cases hx : Source.AXSymbolic.exec op s with
    | none => simp [Source.AXSymbolic.run,hx] at he
    | some mid =>
      simp only [Source.AXSymbolic.run,hx,Option.bind_some] at he
      rw [run,exec_symbolic op s mid hx v tail]
      exact ih mid he
/-- Reuses the exact symbolic run certificate; not yet primitive-source execution. -/
theorem run_actual (v : Fin 6 → V) (tail : V) :
    run PA196.Source.AXProgram.program (materialize v tail Source.AXSymbolic.initial)=
      some (materialize v tail PA196.Source.AXSymbolic.result) :=
  run_symbolic _ _ _ PA196.Source.AXSymbolic.program_symbolic v tail
#print axioms store_registers
#print axioms run_actual
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX

