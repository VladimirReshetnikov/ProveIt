import ObjectComposition

/-!
# Exact object-language targets for bounded rank descent

All executable symbols below are built from `PR` constructors.  No declaration
here adds an axiom or asserts that the general descent compiler is complete.
`RankedDescentGoal` is the proposition the remaining compiler must prove.
-/

namespace LeanProofs.ConciseIPRA.Framework

open Syn
open scoped Fm

namespace Code

def zero (k : Nat) : PR k := .comp .zero Fin.elim0
def one (k : Nat) : PR k := .comp .succ (fun _ => zero k)

def unary (f : PR 1) {n : Nat} (x : PTm n) : PTm n :=
  .app f (fun _ => x)

def binary (f : PR 2) {n : Nat} (x y : PTm n) : PTm n :=
  .app f (Fin.cases x (fun _ => y))

/-- Arguments are count and seed; the result is their sum. -/
def add : PR 2 :=
  .prec (.proj (0 : Fin 1)) (.comp .succ (fun _ => .proj (1 : Fin 3)))

def pred : PR 1 := .prec .zero (.proj (0 : Fin 2))
def isZero : PR 1 := .prec (one 0) (zero 2)

/-- Subtract the first argument from the second by a bounded iteration. -/
def subtractCount : PR 2 :=
  .prec (.proj (0 : Fin 1)) (.comp pred (fun _ => .proj (1 : Fin 3)))

/-- `sub x y = x - y` with truncation at zero. -/
def sub : PR 2 :=
  .comp subtractCount (Fin.cases (.proj (1 : Fin 2)) (fun _ => .proj (0 : Fin 2)))

def le : PR 2 := .comp isZero (fun _ => sub)

/-- The count is argument 0, the initial state argument 1. -/
def iterate (step : PR 1) : PR 2 :=
  .prec (.proj (0 : Fin 1)) (.comp step (fun _ => .proj (1 : Fin 3)))

/-- The fixed PR program `s ↦ iterate step (rank s) s`. -/
def boundedRun (step rank : PR 1) : PR 1 :=
  .comp (iterate step) (Fin.cases rank (fun _ => .proj (0 : Fin 1)))

end Code

def numeralOne {n : Nat} : PTm n := PTm.succ PTm.zero

def holds {n : Nat} (test : PR 1) (x : PTm n) : Fm PTm n :=
  Code.unary test x ≐ numeralOne

def lessEqual {n : Nat} (x y : PTm n) : Fm PTm n :=
  Code.binary Code.le x y ≐ numeralOne

structure RankedSymbols where
  step : PR 1
  rank : PR 1
  terminal : PR 1
  valid : PR 1

namespace RankedSymbols

def run (p : RankedSymbols) {n : Nat} (count state : PTm n) : PTm n :=
  Code.binary (Code.iterate p.step) count state

/-- Counter at 0, initial state at 1.  Every connective is quantifier-free. -/
def budgetInvariant (p : RankedSymbols) : Fm PTm 2 :=
  let state := p.run (var 0) (var 1)
  holds p.valid state ⋏
    (holds p.terminal state ⋎
      lessEqual (Code.binary Code.add (Code.unary p.rank state) (var 0))
        (Code.unary p.rank (var 1)))

theorem budgetInvariant_qf (p : RankedSymbols) : p.budgetInvariant.QF :=
  ⟨trivial, ⟨trivial, trivial⟩⟩

def conclusion (p : RankedSymbols) : Fm PTm 1 :=
  holds p.valid (var 0) ⟶
    holds p.terminal (Code.unary (Code.boundedRun p.step p.rank) (var 0))

def preserveFormula (p : RankedSymbols) : Fm PTm 1 :=
  holds p.valid (var 0) ⟶ holds p.valid (Code.unary p.step (var 0))

def terminalBooleanFormula (p : RankedSymbols) : Fm PTm 1 :=
  (Code.unary p.terminal (var 0) ≐ PTm.zero) ⋎ holds p.terminal (var 0)

def absorbFormula (p : RankedSymbols) : Fm PTm 1 :=
  (holds p.valid (var 0) ⋏ holds p.terminal (var 0)) ⟶
    (Code.unary p.step (var 0) ≐ var 0)

def decreaseFormula (p : RankedSymbols) : Fm PTm 1 :=
  (holds p.valid (var 0) ⋏ (Code.unary p.terminal (var 0) ≐ PTm.zero)) ⟶
    lessEqual (PTm.succ (Code.unary p.rank (Code.unary p.step (var 0))))
      (Code.unary p.rank (var 0))

end RankedSymbols

/-- Required *object-theory proofs* of all local contracts. -/
structure RankedLocalCertificate (p : RankedSymbols) where
  preserve : [] ⊢[PRAAx] p.preserveFormula
  terminalBoolean : [] ⊢[PRAAx] p.terminalBooleanFormula
  absorb : [] ⊢[PRAAx] p.absorbFormula
  decrease : [] ⊢[PRAAx] p.decreaseFormula

/-- The unfinished uniform proof transformation, stated without an axiom. -/
def RankedDescentGoal : Prop :=
  ∀ (p : RankedSymbols), RankedLocalCertificate p →
    (([] : List (Fm PTm 1)) ⊢[PRAAx] p.conclusion)

end LeanProofs.ConciseIPRA.Framework

#print axioms LeanProofs.ConciseIPRA.Framework.RankedSymbols.budgetInvariant_qf
