import Init

/-!
# Elementary expression syntax

STATUS: inspected Lean 4 source, NOT COMPILED in this session.
No semantics, numerical coding, or iPRA proof is asserted by this file.
The grammar matches the language in the requested Richardson theorem.
-/

namespace Richardson

/-- The rational literal `rat numerator denominatorPred` means
`numerator / (denominatorPred + 1)`. Denominators are therefore positive.
Reduced fractions are not required. -/
inductive Expr where
  | rat : Int → Nat → Expr
  | pi : Expr
  | logTwo : Expr
  | var : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | sine : Expr → Expr
  | exponential : Expr → Expr
  | absolute : Expr → Expr

def Expr.substitute (body argument : Expr) : Expr :=
  match body with
  | .rat numerator denominatorPred => .rat numerator denominatorPred
  | .pi => .pi
  | .logTwo => .logTwo
  | .var => argument
  | .add a b => .add (a.substitute argument) (b.substitute argument)
  | .mul a b => .mul (a.substitute argument) (b.substitute argument)
  | .sine a => .sine (a.substitute argument)
  | .exponential a => .exponential (a.substitute argument)
  | .absolute a => .absolute (a.substitute argument)

/-- Composition is syntactic substitution, so it needs no additional node. -/
def Expr.compose (outer inner : Expr) : Expr := outer.substitute inner

def Expr.nodeCount : Expr → Nat
  | .rat _ _ => 1
  | .pi => 1
  | .logTwo => 1
  | .var => 1
  | .add a b => a.nodeCount + b.nodeCount + 1
  | .mul a b => a.nodeCount + b.nodeCount + 1
  | .sine a => a.nodeCount + 1
  | .exponential a => a.nodeCount + 1
  | .absolute a => a.nodeCount + 1

def Expr.zero : Expr := .rat 0 0

def Expr.one : Expr := .rat 1 0

def Expr.neg (e : Expr) : Expr := .mul (.rat (-1) 0) e

def Expr.sub (a b : Expr) : Expr := .add a b.neg

def Expr.natPow (e : Expr) : Nat → Expr
  | 0 => Expr.one
  | n + 1 => .mul e (e.natPow n)

/-- At the semantic level this expression is |f(x)| - f(x).
It is identically zero precisely when f is everywhere nonnegative.
This file defines the syntax only; it does not prove that analytic claim. -/
def Expr.negativePartDetector (f : Expr) : Expr :=
  Expr.sub (.absolute f) f

end Richardson
