# Lean completion plan

## Status

`FiniteUseSemantic.lean` and `ObjectTraceReflection.lean` are source-level
blueprints. The artifact environment had no Lean executable or local checkout
of ProveIt, so neither file is claimed compiler-checked.

## First milestone: compile `ObjectTraceReflection.lean`

1. Add the file under the root `ConciseIPRA` Lake workspace and run the pinned
   toolchain.
2. Resolve any elaboration issue in `app2` / `app3` by giving the `Fin.cases`
   tail functions explicit types.
3. Check the de Bruijn convention in `tracePhi`: variable 0 is the induction
   counter, variable 1 the input parameter.
4. If `tracePhi_qf` does not close by `trivial`, unfold `Fm.QF` and discharge
   the equation/implication cases by `simp [PRTraceSystem.tracePhi]`.
5. If `simpa [phiAtBound]` does not normalize `allE`, prove a dedicated lemma:

   ```lean
   theorem all_tracePhi_at_bound
       (h : ([] : List (Fm PTm 1)) ⊢[PRAAx] Fm.all T.tracePhi) :
       [] ⊢[PRAAx] T.phiAtBound := by
     exact Prf.allE T.boundAtInput h
   ```

   and adjust the definition of `phiAtBound` to be definitionally identical
   to the result.
6. Run `#print axioms traceReflection`.

## Second milestone: raw local obligations

Prove object equations for `T.run`:

- `Run(0,u) = init(u)` from `PRA.precZero`;
- `Run(S i,u) = step(i,Run(i,u),u)` from `PRA.precSucc`.

Define formulas `BaseOK T`, `StepOK T`, and `FinalOK T` corresponding to the
paper's (D0)--(D2). Add a constructor:

```lean
def TraceObligations.ofLocal
    (h0 : [] ⊢[PRAAx] Fm.all (BaseOK T))
    (h1 : [] ⊢[PRAAx] Fm.all (StepOK T))
    (h2 : [] ⊢[PRAAx] Fm.all (FinalOK T)) :
    TraceObligations T := ...
```

The proof is implication introduction/elimination, universal elimination,
Leibniz substitution along the two run equations, and weakening.

## Boolean folds

Implement fixed `PR` symbols for Boolean operations, `allBelow`, `anyBelow`,
first successful search, list lookup, and table update. For each symbol prove
its defining equations and fold introduction/elimination lemmas as actual
`Prf PRAAx` objects. Avoid putting a bounded quantifier inside loop invariants;
use the fold equation instead.

## Relational viability

Start with a rectangular bounded state space. Pair `(resource,state,input)` and
compute a bottom-up table. The deterministic table-filling algorithm is one
`PRTraceSystem`; instantiate `traceReflection` with the invariant that every
filled cell satisfies the viability recurrence. Then prove the least-viable
answer and forward execution as a second trace.

Only after this version compiles, add the sparse external-certificate checker.

## Quantitative modules

1. Signed integer and positive-denominator rational codes.
2. Cross-multiplied equality/order and Boolean reflection.
3. Powers, finite sums/products, abs, min/max.
4. Regular-name sample predicates.
5. Addition, product with magnitude bounds, apartness-guarded inverse.
6. Error-DAG propagation and finite-net argmin.

## End-to-end audit

For each public theorem:

- clean build against the pinned repository revision;
- scan for `sorry`, `admit`, and new line-leading `axiom`;
- `#print axioms`;
- record semantic tests separately from object proof status;
- export through `pra_iff_native` only after the `Prf PRAAx` endpoint compiles.
