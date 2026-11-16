module
public import M6.Source.Semantics
public import M6.Source.AXCode
@[expose] public section
namespace M6.Source.AXMacro

inductive Op where
  | push | cons | copyA | copyD | copyH | incT | readH | readD
  deriving DecidableEq, Repr

structure Store where
  t : Nat
  a : Nat
  d : Nat
  h : Nat
  l : Nat
  stack : List Nat
  deriving DecidableEq, Repr

def exec : Op → Store → Option Store
  | .push, s => some {s with t := 0, stack := s.t :: s.stack}
  | .cons, s => match s.stack with
    | [] => none
    | v :: vs => some {s with t := AXCode.wim v s.t, stack := vs}
  | .copyA, s => some {s with t := s.t+s.a}
  | .copyD, s => some {s with t := s.t+s.d}
  | .copyH, s => some {s with t := s.t+s.h}
  | .incT, s => some {s with t := s.t+1}
  | .readH, s => some {s with h := s.h+(Cantor.decode s.l).1, l := (Cantor.decode s.l).2}
  | .readD, s => some {s with d := s.d+(Cantor.decode s.l).1, l := (Cantor.decode s.l).2}

def run : List Op → Store → Option Store
  | [], s => some s
  | op :: ops, s => (exec op s).bind (run ops)

/-- Fully materialized clean-scratch physical store, with an arbitrary stack tail. -/
def registers (s : Store) (bottom : Nat) (f : Registers) : Registers := fun r =>
  if r=1 then s.t else if r=2 then AXCode.stackCode s.stack bottom else
  if r=3 then s.a else if r=4 then s.d else if r=5 then s.h else
  if r=6 then 0 else if r=7 then 0 else if r=8 then s.l else f r

def configAt (pc : Nat) (s : Store) (bottom : Nat) (f : Registers) : Configuration :=
  ⟨.at pc, registers s bottom f⟩
end M6.Source.AXMacro

