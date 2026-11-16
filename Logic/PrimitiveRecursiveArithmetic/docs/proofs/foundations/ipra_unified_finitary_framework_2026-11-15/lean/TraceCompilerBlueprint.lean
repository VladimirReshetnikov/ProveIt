import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Proof-producing finite-trace compiler: object-language blueprint

STATUS: intentionally incomplete Lean blueprint.  The definitions and theorem
signatures are designed for the ProveIt `ConciseIPRA` API at commit
`b88e843c31b50dfe461bfbd0380166ca422cd3ab`.  This file was not compiled in
the artifact environment; `sorry` marks exactly the object-language formula
plumbing and derivations still to construct.  It must not be cited as a
kernel-checked theorem.

The key improvement over a semantic trace theorem is the type of the premises
and result: they are `Prf PRAAx` derivations.  The final theorem is intended to
be a function that computes the global derivation from local derivations.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.Finitary

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Fixed primitive-recursive symbols of a one-parameter trace system. -/
structure PRTraceSystem where
  good   : PR 1
  init   : PR 1
  bound  : PR 1
  step   : PR 3       -- arguments: recursion index, previous state, input u
  inv    : PR 3       -- arguments: index, state, input u
  accept : PR 2       -- arguments: state, input u

/-- The actual run symbol. `PR.prec` has one recursion argument and one
parameter, so the step receives `(i, previous, u)`. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

/-- Object-language Boolean truth.  Production code should reuse the canonical
Boolean code selected for the shared finite library. -/
def IsOne {n : Nat} (t : PTm n) : Fm PTm n :=
  t ≐ succ zero

/-!
## Required application helpers

Implement helpers `app1`, `app2`, and `app3` using `Fin.cases`, together with
named de Bruijn variables.  Fix and document the variable layouts:

* `BaseFm T : Fm PTm 1` uses `[u]`;
* `StepFm T : Fm PTm 3` uses `[i, s, u]`;
* `FinalFm T : Fm PTm 2` uses `[s, u]`;
* the induction formula `InvRunFm T : Fm PTm 2` uses `[i, u]`.

The intended formulas are:

```
BaseFm  := Good(u) -> Inv(0, init(u), u)
StepFm  := Good(u) -> Inv(i,s,u) -> Inv(S i, step(i,s,u),u)
FinalFm := Good(u) -> Inv(bound(u),s,u) -> Accept(s,u)
InvRunFm := Inv(i, run(i,u), u)
ResultFm := forall u, Good(u) -> Accept(run(bound(u),u),u)
```

All induction formulas are quantifier free.
-/

/-- Base local formula. -/
def BaseFm (T : PRTraceSystem) : Fm PTm 1 := by
  -- Construct the displayed formula using `PTm.app`, `Fm.imp`, and `IsOne`.
  sorry

/-- Local preservation formula. -/
def StepFm (T : PRTraceSystem) : Fm PTm 3 := by
  sorry

/-- Final soundness formula. -/
def FinalFm (T : PRTraceSystem) : Fm PTm 2 := by
  sorry

/-- Quantifier-free induction formula, with free variables `(i,u)`. -/
def InvRunFm (T : PRTraceSystem) : Fm PTm 2 := by
  sorry

/-- Closed result formula. -/
def ResultFm (T : PRTraceSystem) : Fm PTm 0 := by
  sorry

/-- The local obligations are themselves embedded iPRA proofs. -/
structure TraceProofs (T : PRTraceSystem) where
  base  : ([] : List (Fm PTm 1)) ⊢[PRAAx] BaseFm T
  step  : ([] : List (Fm PTm 3)) ⊢[PRAAx] StepFm T
  final : ([] : List (Fm PTm 2)) ⊢[PRAAx] FinalFm T

/-- Main target: construct the global object-language proof from the local
object-language proofs. -/
def traceReflection (T : PRTraceSystem) (h : TraceProofs T) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] ResultFm T := by
  /-
  Completion path, using only existing `ConciseIPRA` constructors:

  1. Work first with free `u` and context `[Good(u)]`.
  2. Instantiate `h.base` at `u`; rewrite `T.run(0,u)` with
     `PRA.precZero`; transport equality with `Prf.eqSubst1`.
  3. For the induction step, use context `[InvRun(i,u), Good(u)]`.
     Instantiate `h.step` at `(i, run(i,u), u)` and eliminate implications.
     Rewrite the successor run using `PRA.precSucc`.
  4. Apply `PRA.qfInd` to `InvRunFm T`, with the free parameter `u`.
     The syntactic side condition follows by reducing `Fm.qf` for the
     equation-valued formula.
  5. Specialize the resulting universal invariant at `T.bound(u)`.
  6. Instantiate `h.final` at `(run(bound(u),u),u)` and cut.
  7. Discharge `Good(u)` with `Prf.impI`, then introduce `u` with `Prf.allI`.

  `Prf.subst`, `Prf.weaken`, `Prf.trans`, `Prf.allE`, `Prf.impE`, and the
  primitive-recursion equation proofs are the principal APIs.  Keep a small
  lemma library for repeated de Bruijn substitutions rather than unfolding
  them in every application.
  -/
  sorry

/-- Final transport is already checked by the repository once the ordinary
object-language derivation exists. -/
def traceReflectionNative (T : PRTraceSystem) (h : TraceProofs T) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (ResultFm T)) := by
  exact (pra_iff_native).mp (traceReflection T h)

/-!
## Follow-on compiler

Define a finite-program DSL with constructors for pure PR assignments,
sequential composition, bounded loops, guarded branches, and checks.  Compile
it to `PRTraceSystem`; pair each syntax node with local `Prf PRAAx` contracts.
Structural recursion on the certified program should call `traceReflection`
and compose proofs with `Prf.trans`.  This gives a proof-producing compiler,
not a reflection theorem for arbitrary Lean code.
-/

end LeanProofs.ConciseIPRA.Finitary
