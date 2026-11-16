import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation
import ObjectTraceCompiler

/-!
# A finite proof-producing program language

Blueprint only; not compiled in the artifact environment.  The syntax is
finite and structural.  It does not postulate a total universal primitive-
recursive evaluator: every closed syntax tree compiles at the Lean meta-level
to fixed `PR` symbols and fixed `Prf PRAAx` derivation constructors.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FinitaryInterface

open Syn
open scoped Fm
open PTm (app)

/-- Fixed low-level symbols used by the structural compiler. -/
structure ProgramLibrary where
  pair : PR 2
  ite  : PR 3  -- Boolean test, yes value, no value

/-- A Nat-coded, one-output program with `n` numerical inputs.  Products,
lists, matrices, finite clouds, and demand tables use fixed PR codings. -/
inductive FProg : Nat → Type
  | atom {n : Nat} (f : PR n) : FProg n
  | pair {n : Nat} (p q : FProg n) : FProg n
  | comp {n : Nat} (outer : FProg 1) (inner : FProg n) : FProg n
  | guard {n : Nat} (test : PR n) (yes no : FProg n) : FProg n
  | loop {n : Nat} (init : PR n) (bound : PR n)
      (step : PR (n + 2)) : FProg n
  | search {n : Nat} (bound : PR n)
      (predicate : PR (n + 1)) : FProg n

/-- Structural compilation to a fixed primitive-recursive symbol. -/
def FProg.compile (L : ProgramLibrary) : {n : Nat} → FProg n → PR n
  | _, .atom f => f
  | _, .pair p q =>
      .comp L.pair (Fin.cases (p.compile L) (fun _ => q.compile L))
  | _, .comp outer inner =>
      .comp (outer.compile L) (fun _ => inner.compile L)
  | _, .guard test yes no =>
      .comp L.ite
        (Fin.cases test (Fin.cases (yes.compile L) (fun _ => no.compile L)))
  | n, .loop init bound step => by
      -- Build the run by `PR.prec`, then compose it with the compiled bound and
      -- the input variables.  The state may encode a demand table and validity
      -- accumulator.  Only finite arity shuffles remain.
      sorry
  | n, .search bound predicate => by
      -- Prefix scan carrying `(found,index)`; default to `bound` when absent.
      sorry

/-- A first-order contract.  In `post`, variable zero is the output and the
remaining variables are the shifted inputs. -/
structure ProgContract (n : Nat) where
  pre : Fm PTm n
  post : Fm PTm (n + 1)
  postQF : post.QF

/-- Substitute the compiled output into variable zero of the postcondition. -/
def ProgContract.result (L : ProgramLibrary) {n : Nat}
    (C : ProgContract n) (P : FProg n) : Fm PTm n :=
  C.post.subst (Fin.cases (app (P.compile L) (fun i => var i)) (fun i => var i))

/-- Exact proof-carrying boundary: the field is already an object-language
derivation, not a semantic Lean theorem.  Constructors for atoms, composition,
guards, loops, and search build this record structurally. -/
structure CertifiedProg (L : ProgramLibrary) (n : Nat) where
  program : FProg n
  contract : ProgContract n
  sound : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (contract.pre ⟶ contract.result L program)

/-- The public correctness theorem is just the proof assembled by the
structural compiler. -/
theorem compileCertifiedProgram {L : ProgramLibrary} {n : Nat}
    (P : CertifiedProg L n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      (P.contract.pre ⟶ P.contract.result L P.program) :=
  P.sound

/-!
Constructor plan:

* `atom`: consume a supplied local `Prf PRAAx` contract;
* `pair` and `comp`: use substitution and `Prf.trans`;
* `guard`: use Boolean test reflection; for approximate branch data use a
  relational union rather than an exact guard;
* `loop`: lower to `PRTraceSystem` and call `traceReflection`;
* `search`: use the shared bounded-fold and least-witness theorems;
* static DAG: compile reverse demand propagation and the forward table pass as
  two bounded loops, then call `traceReflection` once.
-/

end LeanProofs.ConciseIPRA.FinitaryInterface
