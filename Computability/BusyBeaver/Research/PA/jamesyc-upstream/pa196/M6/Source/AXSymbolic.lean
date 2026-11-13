module
public import M6.Source.AXMacroProgram
@[expose] public section
set_option linter.unusedSimpArgs false
namespace M6.Source.AXSymbolic
abbrev Op := AXMacro.Op
inductive Expr where
  | zero | atom (i : Fin 6) | succ (x : Expr) | add (x y : Expr) | im (x y : Expr)
  deriving DecidableEq, Repr

def plus : Expr → Expr → Expr
  | .zero, y => y
  | x, .zero => x
  | x, y => .add x y

def eval (v : Fin 6 → Nat) : Expr → Nat
  | .zero => 0
  | .atom i => v i
  | .succ x => eval v x + 1
  | .add x y => eval v x + eval v y
  | .im x y => AXCode.wim (eval v x) (eval v y)

theorem eval_plus (v : Fin 6 → Nat) (x y : Expr) :
    eval v (plus x y) = eval v x + eval v y := by
  cases x <;> cases y <;> simp [plus,eval,Nat.zero_add]

structure Store where
  t : Expr
  a : Expr
  d : Expr
  h : Expr
  fields : List Expr
  stack : List Expr
  deriving DecidableEq, Repr

def exec : Op → Store → Option Store
  | .push, s => some {s with t := .zero, stack := s.t :: s.stack}
  | .cons, s => match s.stack with
    | [] => none
    | v :: vs => some {s with t := .im v s.t, stack := vs}
  | .copyA, s => some {s with t := plus s.t s.a}
  | .copyD, s => some {s with t := plus s.t s.d}
  | .copyH, s => some {s with t := plus s.t s.h}
  | .incT, s => some {s with t := .succ s.t}
  | .readH, s => match s.fields with
    | [] => none
    | v :: vs => some {s with h := plus s.h v, fields := vs}
  | .readD, s => match s.fields with
    | [] => none
    | v :: vs => some {s with d := plus s.d v, fields := vs}

def run : List Op → Store → Option Store
  | [], s => some s
  | op :: ops, s => (exec op s).bind (run ops)

def materialize (v : Fin 6 → Nat) (tail : Nat) (s : Store) : AXMacro.Store :=
  ⟨eval v s.t,eval v s.a,eval v s.d,eval v s.h,
    AXCode.stackCode (s.fields.map (eval v)) tail,s.stack.map (eval v)⟩

theorem exec_sound (op : Op) (s s' : Store) (he : exec op s = some s')
    (v : Fin 6 → Nat) (tail : Nat) :
    AXMacro.exec op (materialize v tail s) = some (materialize v tail s') := by
  cases op <;> cases s with
  | mk t a d h fields stack =>
    cases fields <;> cases stack <;>
      simp only [exec,Option.some.injEq] at he <;> cases he <;>
      simp_all [materialize,AXMacro.exec,eval,eval_plus,AXCode.stackCode,Cantor.decode_pair]

theorem run_sound (ops : List Op) (s s' : Store) (he : run ops s = some s')
    (v : Fin 6 → Nat) (tail : Nat) :
    AXMacro.run ops (materialize v tail s) = some (materialize v tail s') := by
  induction ops generalizing s with
  | nil =>
    simp only [run,Option.some.injEq] at he
    subst s'
    rfl
  | cons op ops ih =>
    cases hx : exec op s with
    | none => simp [run,hx] at he
    | some mid =>
      simp only [run,hx,Option.bind_some] at he
      rw [AXMacro.run,exec_sound op s mid hx v tail]
      exact ih mid he
end M6.Source.AXSymbolic

