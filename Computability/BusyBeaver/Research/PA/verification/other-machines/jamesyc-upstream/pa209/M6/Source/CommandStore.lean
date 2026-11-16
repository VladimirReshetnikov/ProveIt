module
public import M6.Source.Enumeration
public import M6.Source.ActualAXCode
public import M6.Source.Semantics
@[expose] public section
namespace M6.Source
open Cantor Enumeration

/-- Arithmetic boundary state shared by literal-source macro transfer. This is
not a second native proof calculus; PA's interpreter uses an explicit conversion. -/
structure CommandStore where
  t : Nat
  w : Nat
  d : Nat
  h : Nat
  deriving DecidableEq, Repr

/-- Exact actual AX profile, with the same S and MP arithmetic. A `none` result
means the S sum-one guard halted, not an undefined arithmetic operation. -/
def commandEval : Command → CommandStore → Option CommandStore
  | .shift,s => if s.t+s.h = 1 then none else
      some ⟨s.h,(decode s.w).2,s.d,(decode s.w).1⟩
  | .mp x,s =>
      let y := s.d+x
      if AXCode.wim s.t y = s.h then some ⟨y,pair 0 s.w,y,0⟩ else some ⟨0,s.w,y,0⟩
  | .ax c x y,s => some ⟨ActualAXCode.gate (s.d+x) (s.h+y) c,
      (ActualAXCode.pa135Heads (s.d+x) (s.h+y) c s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩

def commandsEval : List Command → CommandStore → Option CommandStore
  | [],s => some s
  | c::cs,s => (commandEval c s).bind (commandsEval cs)

theorem commandsEval_append (xs ys : List Command) (s : CommandStore) :
    commandsEval (xs++ys) s = (commandsEval xs s).bind (commandsEval ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,commandsEval]
    cases h : commandEval x s <;> simp [ih]

def commandInitial : CommandStore :=
  ⟨ActualAXCode.gate 0 0 0,(ActualAXCode.pa135Heads 0 0 0 0 0 ++ [1]).foldr pair 1,0,0⟩

def commandRegisters (n l a : Nat) (s : CommandStore) : Registers :=
  fun r => [n,s.t,s.w,a,s.d,s.h,0,0,l].getD r.val 0

def commandConfig (pc n l a : Nat) (s : CommandStore) : Configuration :=
  ⟨.at pc,commandRegisters n l a s⟩

#print axioms commandsEval_append
end M6.Source

