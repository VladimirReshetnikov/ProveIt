module
public import M6.Source.Syntax

@[expose] public section

namespace M6.Source

abbrev Registers := Fin 9 → Nat

inductive Control where
  | at (ordinal : Nat)
  | exited
  | halted
  | malformed
  deriving DecidableEq, Repr

structure Configuration where
  control : Control
  registers : Registers

/-- Register replacement, not an assumption that untouched registers are zero. -/
def write (registers : Registers) (r : Fin 9) (v : Nat) : Registers :=
  fun k => if k = r then v else registers k

def destination : Option Nat → Control
  | some n => .at n
  | none => .exited

def execute (instruction : Instruction) (registers : Registers) : Configuration :=
  match instruction with
  | .inc r n => ⟨destination n, write registers r (registers r + 1)⟩
  | .dec r z n =>
      if registers r = 0 then ⟨destination z, registers⟩
      else ⟨destination n, write registers r (registers r - 1)⟩
  | .jump n => ⟨destination n, registers⟩
  | .halt => ⟨.halted, registers⟩

/-- Terminal controls are absorbing. Failed decoding is distinct from normal
exit and halt; it is never treated as a successful source execution. -/
def step (sites : Array Site) (c : Configuration) : Configuration :=
  match c.control with
  | .at n => match resolveAt sites n with
      | some instruction => execute instruction c.registers
      | none => ⟨.malformed, c.registers⟩
  | _ => c

theorem step_of_resolved (h : resolveAt sites n = some instruction) (r : Registers) :
    step sites ⟨.at n, r⟩ = execute instruction r := by
  simp only [step, h]

inductive Steps (sites : Array Site) : Nat → Configuration → Configuration → Prop
  | refl (c) : Steps sites 0 c c
  | cons : Steps sites n (step sites a) b → Steps sites (n + 1) a b

end M6.Source

