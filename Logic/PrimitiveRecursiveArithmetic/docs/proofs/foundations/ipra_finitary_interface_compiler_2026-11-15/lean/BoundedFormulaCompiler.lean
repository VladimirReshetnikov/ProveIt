import ConciseIPRA.PR
import ObjectTraceCompiler

/-!
# Bounded formulas and Boolean compilation

Blueprint only; not compiled in the artifact environment.

Every *fixed* formula generated from primitive-recursive atomic relations,
intuitionistic propositional connectives, and bounded quantifiers compiles to a
fixed primitive-recursive Boolean symbol.  The object-language reflection proof
reduces bounded quantifiers to folds and yields a quantifier-free equation
suitable for `PRA.qfInd`.  This is structural compilation, not a universal PR
evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FinitaryInterface

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Meta-syntax for a fixed bounded formula with `n` free numerical inputs.
Atomic predicates are represented by Boolean-valued primitive-recursive
symbols. -/
inductive BFm : Nat → Type
  | atom {n k : Nat} (p : PR k) (args : Fin k → PR n) : BFm n
  | falsum {n : Nat} : BFm n
  | and {n : Nat} (a b : BFm n) : BFm n
  | or {n : Nat} (a b : BFm n) : BFm n
  | imp {n : Nat} (a b : BFm n) : BFm n
  | allLt {n : Nat} (bound : PR n) (body : BFm (n + 1)) : BFm n
  | exLt {n : Nat} (bound : PR n) (body : BFm (n + 1)) : BFm n

/-- Required fixed Boolean library.  Each symbol is total on all natural-number
inputs.  Its intended values on Boolean inputs are specified by `BoolProofs`. -/
structure BoolPR where
  falseB : PR 0
  trueB  : PR 0
  notB   : PR 1
  andB   : PR 2
  orB    : PR 2
  impB   : PR 2
  eqB    : PR 2
  ltB    : PR 2

/-- Turn an `n`-ary primitive-recursive symbol into the term obtained by
applying it to all free variables in index order. -/
def prTerm {n : Nat} (f : PR n) : PTm n :=
  app f (fun i => var i)

/-- Boolean less-than as an object-language formula. -/
def LtFm (B : BoolPR) {n : Nat} (s t : PTm n) : Fm PTm n :=
  IsTrue (app2 B.ltB s t)

/-- Prefix conjunction and prefix disjunction.  The body is already a fixed
symbol of arity `n+1`; the fold result has arity `n+1`, taking the bound as its
first argument and the `n` parameters afterward. -/
def allFold (_B : BoolPR) {n : Nat} (_body : PR (n + 1)) : PR (n + 1) := by
  -- Build by `PR.prec`: base is true; step conjoins the previous accumulator
  -- with `body(i, parameters)`.  Only finite arity shuffles remain.
  sorry


def anyFold (_B : BoolPR) {n : Nat} (_body : PR (n + 1)) : PR (n + 1) := by
  -- Base is false; step disjoins the previous accumulator with the body.
  sorry

/-- Compilation target.  The bounded cases evaluate the fixed fold at the
compiled bound and the current parameters. -/
def BFm.compile (B : BoolPR) : {n : Nat} → BFm n → PR n
  | _, .atom p args => .comp p args
  | _, .falsum => .comp B.falseB Fin.elim0
  | _, .and a b =>
      .comp B.andB (Fin.cases (a.compile B) (fun _ => b.compile B))
  | _, .or a b =>
      .comp B.orB (Fin.cases (a.compile B) (fun _ => b.compile B))
  | _, .imp a b =>
      .comp B.impB (Fin.cases (a.compile B) (fun _ => b.compile B))
  | n, .allLt bound body => by
      -- Compose `allFold B (body.compile B)` with `(bound, parameters)`.
      -- The result has arity `n`; implement the displayed arity shuffle.
      sorry
  | n, .exLt bound body => by
      -- Compose `anyFold B (body.compile B)` with `(bound, parameters)`.
      sorry

/-- Ordinary first-order reading of the bounded meta-syntax.  Bounded
quantifiers expand to an unbounded quantifier guarded by the Boolean `<` test.
This formula is used only in the reflection statement; induction is performed
on the compiled quantifier-free equation. -/
def BFm.toFm (B : BoolPR) : {n : Nat} → BFm n → Fm PTm n
  | _, .atom p args => IsTrue (prTerm (.comp p args))
  | _, .falsum => Fm.bot
  | _, .and a b => a.toFm B ⋏ b.toFm B
  | _, .or a b => a.toFm B ⋎ b.toFm B
  | _, .imp a b => a.toFm B ⟶ b.toFm B
  | _, .allLt bound body =>
      Fm.all (LtFm B (var 0) (Syn.shift (prTerm bound)) ⟶ body.toFm B)
  | _, .exLt bound body =>
      Fm.ex (LtFm B (var 0) (Syn.shift (prTerm bound)) ⋏ body.toFm B)

/-- The quantifier-free compiled reading. -/
def BFm.compiledFm (B : BoolPR) {n : Nat} (a : BFm n) : Fm PTm n :=
  IsTrue (prTerm (a.compile B))

/-- Object-language proof package for the fixed Boolean library.  A production
version expands `laws` into closed `Prf PRAAx` fields for Boolean range, truth
tables, less-than reflection, and the zero/successor equations of both folds. -/
structure BoolProofs (B : BoolPR) where
  laws : Prop

/-- Main target: the ordinary bounded formula is provably equivalent in iPRA
to one quantifier-free equation. -/
theorem boundedFormulaReflection
    (B : BoolPR) (hB : BoolProofs B) {n : Nat} (a : BFm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      Fm.iff (a.toFm B) (a.compiledFm B) := by
  /-
  Structural induction on `a`.

  * atoms and propositional cases use the corresponding `BoolProofs` fields;
  * `allLt` uses qf induction on the prefix-conjunction fold;
  * `exLt` uses qf induction on the prefix-disjunction fold;
  * `Prf.iffTrans`, substitution, and congruence assemble the result.
  -/
  sorry

/-- Immediate side product used by loop compilers: compiled truth is an atomic
quantifier-free equation. -/
theorem compiledFm_qf (B : BoolPR) {n : Nat} (a : BFm n) :
    (a.compiledFm B).QF := by
  simp [BFm.compiledFm, IsTrue, Fm.QF]

end LeanProofs.ConciseIPRA.FinitaryInterface
