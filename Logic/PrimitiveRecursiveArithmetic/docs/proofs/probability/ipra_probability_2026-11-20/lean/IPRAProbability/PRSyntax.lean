import Std

/-!
Typed syntax and finite evaluation derivations for primitive recursion.

This file deliberately defines no universal evaluator and no assertion that
all natural-number functions are primitive recursive.  `Eval` is a graph
relation.  A fixed closed syntax tree can be translated into function
symbols and defining equations of iPRA.  A universal total evaluation
function on arbitrary codes must NOT be introduced as a primitive-recursive
function.
-/

namespace IPRAProbability

/-- Arity-indexed primitive-recursive syntax.  Arguments of a recursion are
`(time, parameters)`; arguments of its step are `(time, previous, parameters)`.
-/
inductive PR : Nat → Type where
  | zero (n : Nat) : PR n
  | succ : PR 1
  | proj (n : Nat) (i : Fin n) : PR n
  | comp {n m : Nat} (outer : PR m) (inner : Fin m → PR n) : PR n
  | primrec {n : Nat} (base : PR n) (step : PR (n + 2)) : PR (n + 1)

/-- Prepend one argument to a fixed-length tuple. -/
def argsCons {n : Nat} (a : Nat) (xs : Fin n → Nat) : Fin (n + 1) → Nat :=
  Fin.cases a xs

/-- Finite evaluation derivations, not a universal primitive-recursive interpreter. -/
inductive Eval : {n : Nat} → PR n → (Fin n → Nat) → Nat → Prop where
  | zero {n : Nat} (xs : Fin n → Nat) : Eval (.zero n) xs 0
  | succ (xs : Fin 1 → Nat) : Eval .succ xs (xs 0 + 1)
  | proj {n : Nat} (i : Fin n) (xs : Fin n → Nat) : Eval (.proj n i) xs (xs i)
  | comp {n m : Nat} (outer : PR m) (inner : Fin m → PR n)
      (xs : Fin n → Nat) (ys : Fin m → Nat) (z : Nat)
      (args : ∀ i, Eval (inner i) xs (ys i))
      (body : Eval outer ys z) : Eval (.comp outer inner) xs z
  | rec_zero {n : Nat} (base : PR n) (step : PR (n + 2))
      (xs : Fin n → Nat) (y : Nat) (h : Eval base xs y) :
      Eval (.primrec base step) (argsCons 0 xs) y
  | rec_succ {n : Nat} (base : PR n) (step : PR (n + 2))
      (xs : Fin n → Nat) (t y z : Nat)
      (previous : Eval (.primrec base step) (argsCons t xs) y)
      (next : Eval step (argsCons t (argsCons y xs)) z) :
      Eval (.primrec base step) (argsCons (t + 1) xs) z

/-- A *metatheoretic* connection between a function and one fixed PR syntax tree.
Its proof field does not mean that an arbitrary Lean function is admitted by iPRA.
No generic constructor for this structure is provided.
-/
structure FixedPRFunction (n : Nat) where
  code : PR n
  value : (Fin n → Nat) → Nat
  graph : ∀ xs, Eval code xs (value xs)

/-- The identity program is an explicit certified primitive-recursive example. -/
def identityProgram : FixedPRFunction 1 where
  code := .proj 1 0
  value := fun xs => xs 0
  graph := fun xs => Eval.proj 0 xs

/-- Successor is another explicit certified primitive-recursive example. -/
def successorProgram : FixedPRFunction 1 where
  code := .succ
  value := fun xs => xs 0 + 1
  graph := Eval.succ

end IPRAProbability
