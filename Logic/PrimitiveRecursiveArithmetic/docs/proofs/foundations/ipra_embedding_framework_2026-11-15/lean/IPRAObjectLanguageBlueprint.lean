import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation
import ConciseIPRA.NativePublic

/-!
# Object-language blueprint for Certified Finitary Presentations

STATUS: formalization outline, intentionally incomplete.  The declarations
below isolate the definitions and proof obligations; `sorry` marks exactly the
embedded derivations that must be constructed.  No theorem in this file should
be cited as kernel-checked until it has been built in the pinned ProveIt
workspace and audited with `#print axioms`.

The central design choice is to code all run-time data into one natural `u`.
A trace system then has fixed primitive-recursive symbols:

* `good u` - Boolean finite input table;
* `init u` - initial state;
* `bound u` - number of iterations;
* `step(i,s,u)` - next state (the argument order used by `PR.prec`);
* `inv(i,s,u)` - Boolean invariant;
* `accept(s,u)` - final Boolean conclusion.

The global represented-object hypotheses are not put into the induction
formula.  They are first instantiated at the finitely many queried precisions
to prove `good u = 1`.  The induction formula is the quantifier-free equation
`good u = 1 -> inv(i, run(i,u), u) = 1`.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.CFP

open Syn
open scoped Fm
open PTm (app zero succ)

/-- Fixed primitive-recursive symbols of a one-code trace system. -/
structure PRTraceSystem where
  good : PR 1
  init : PR 1
  bound : PR 1
  step : PR 3
  inv : PR 3
  accept : PR 2

/-- The run symbol.  With one parameter `u`, primitive recursion has arity two
and receives `(i, previous, u)` in its step equation. -/
def PRTraceSystem.run (T : PRTraceSystem) : PR 2 :=
  .prec T.init T.step

/-- Object-language Boolean truth.  A production version should use the
repository's established Boolean coding library and its proved normalization
lemmas rather than introducing a second Boolean convention. -/
def IsOne {n : Nat} (t : PTm n) : Fm PTm n := t ≐ succ zero

/-!
## Main embedded obligations

For a concrete `T`, define the following closed/open formulas explicitly:

```
Good(u)       := IsOne (app T.good [u])
Run(i,u)      := app T.run [i,u]
Inv(i,u)      := IsOne (app T.inv [i,Run(i,u),u])
Accept(u)     := IsOne (app T.accept [Run(bound(u),u),u])
```

Then construct these derivations:

1. `base`:
   `Good(u) |- Inv(0,u)`.
2. `step`:
   `Good(u), Inv(i,u) |- Inv(S i,u)`.
   The defining equation `PRA.precSucc` rewrites the run term.
3. `run_inv`:
   `Good(u) |- forall i, Inv(i,u)` by `PRA.qfInd`.
4. `final`:
   `Good(u), Inv(bound(u),u) |- Accept(u)`.
5. `trace_reflection`:
   `|- forall u, Good(u) -> Accept(u)`.

The formulas in 1--4 are quantifier free.  Any bounded universal condition in
an invariant is represented by a primitive-recursive Boolean fold and hence by
an equation to `1`.
-/

/-- Target theorem: generic finite-trace reflection, parameterized by supplied
embedded base/step/final derivations.  The exact record of premises is left to
be implemented after reusing the Boolean and tuple libraries selected for the
project. -/
theorem trace_reflection_target (T : PRTraceSystem) : True := by
  -- Implementation path:
  -- * instantiate `PRA.precZero` and `PRA.precSucc` for `T.run`;
  -- * apply `PRA.qfInd` to the equation-valued invariant;
  -- * specialize at `T.bound u` and compose with final soundness;
  -- * introduce `u` universally.
  trivial

/-!
## Represented-object layer

For each fixed evaluator symbol `a : PR (r+1)`, define formulas rather than a
higher-type object inside iPRA:

```
Regular_a(p) := forall k l,
  qdist(a(p,k), a(p,l)) <= 2^-k + 2^-l.
EqName_a_b(p) := forall k l,
  qdist(a(p,k), b(p,l)) <= 2^-k + 2^-l.
Apart_a_b(p,d) := d>0 and forall k l,
  d <= qdist(a(p,k), b(p,l)) + 2^-k + 2^-l.
```

Operations are fixed `PR` symbols plus a primitive-recursive precision
transformer.  Their correctness theorem is another instance of finite-trace
reflection.  A theorem polymorphic in an arbitrary evaluator is a Lean-level
schema generator, not a single first-order iPRA sentence.
-/

/-- Final transport is already supplied by the repository. -/
theorem transport_finished_pra_proof {n : Nat} {Gamma : List (Fm PTm n)}
    {phi : Fm PTm n} (h : Gamma ⊢[PRAAx] phi) :
    NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA phi) :=
  (pra_iff_native).mp h

/-!
## Completion checklist

* Reuse or implement object-language codes for signed integers, positive-
  denominator rationals, lists, tuples, Booleans, and finite folds.
* Prove the fold equations and comparison correctness by `PRA.qfInd`.
* Implement `GoodTable`: the Boolean conjunction of precisely the input-name
  samples requested by the trace.
* Prove the fixed-precision theorem with precision as a free variable; apply
  universal introduction only after the finite trace proof.
* Add robust branch, finite-net search, and height-bound/list modules as
  separate trace systems.
* Only after obtaining an actual `Prf PRAAx` endpoint invoke
  `pra_iff_native`; an ambient theorem about `Nat`, `Rat`, or `Real` is not a
  substitute.
-/

end LeanProofs.ConciseIPRA.CFP
