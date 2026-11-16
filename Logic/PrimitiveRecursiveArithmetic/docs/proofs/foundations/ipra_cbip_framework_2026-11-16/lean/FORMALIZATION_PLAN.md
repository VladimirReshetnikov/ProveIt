# CBIP formalization plan

## Goal

Turn fixed Certified Bounded Interaction Programs into explicit derivations

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] theoremSentence
```

and only then use `pra_iff_native` for optional transport.

## Audited dependencies

- `ConciseIPRA.PR`: `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, recursion equations.
- `ConciseIPRA.Deduction`: substitution, weakening, cut, implication and quantifier rules, equality transport.
- `IPRADerivations.Core.Basic`: `inst`, open `ind`, congruence helpers, arithmetic defining equations.
- `IPRADerivations.Core.Pairing`: pairing and projections.
- `IPRADerivations.Core.Search`: checked least bounded search and minimality.
- `IPRADerivations.Core.Order`, `BoundedSums`, `MultiSums`: finite comparisons/folds.
- The stable-observable packet's compiled inference-rule pattern can be promoted or reproduced locally.

## Milestone 1: normalized trace kernel

Place `NormalizedTraceReflection.lean` under the ProveIt Lake workspace and compile it. Resolve only elaboration-level issues (likely `simpa` normal forms or namespace qualification). Do not weaken its theorem statement.

Acceptance criteria:

- clean build;
- no `sorry`, `admit`, or new axioms;
- `#print axioms traceReflectionNormalized` contains only the metatheoretic axioms already present in the repository;
- native transport compiles after the PRA theorem.

## Milestone 2: raw-to-normalized elaboration

Port the `PRTraceSystem`, `BaseFm`, `StepFm`, and `FinalFm` definitions from the prior object trace compiler. Implement:

```lean
def normalizeRaw (T : PRTraceSystem) :
  RawTraceProofs T -> NormalizedTraceProofs T
```

Use:

1. `IPRADerivations.inst` to instantiate closed local contracts;
2. `PRA.precZero`/`PRA.precSucc` for runner equations;
3. `Prf.impE`, `Prf.impI`, `Prf.hyp0`, weakening;
4. `Prf.eqCongr` and `Prf.eqSubst1` for state transport.

Keep each of the three fields in a separate theorem so substitution failures remain local.

## Milestone 3: Boolean fold API

Choose one canonical encoding and prove object-level rules for:

- Boolean normalization, not/and/or;
- `allBelow`, `anyBelow`;
- least success with a sentinel;
- finite list length, lookup, append, update;
- finite maximum, sum, product, and argmin.

Favor introduction/elimination equations over large biconditionals. For example:

```text
allBelow p (n+1) = 1 -> allBelow p n = 1
allBelow p (n+1) = 1 -> p n = 1
allBelow p n = 1 -> p n = 1 -> allBelow p (n+1) = 1
```

These are directly useful in quantifier-free invariants.

## Milestone 4: bounded strategy compiler

Start with a single fixed formula of the form `forall q < Q, exists z < Z, forall e < E, R`. Generate:

- Boolean value;
- canonical success/failure certificate;
- checker;
- object proofs of checker soundness on both sides.

Then abstract by metatheoretic structural recursion over fixed bounded formula syntax. Do not postulate an object-level universal formula evaluator.

## Milestone 5: relational viability

Implement a rectangular table bounded by `stateBound`.

1. reverse row recurrence;
2. viability correctness by `PRA.qfInd` on resource;
3. least viable answer using checked `Search`;
4. forward replay as a normalized trace;
5. terminal postcondition;
6. optional sparse certificate checker.

## Milestone 6: stable observers

Implement or promote the five-line logical combinators for:

- extracting a terminal certificate from a bounded invariant;
- combining independent certificate derivations;
- discharging certificate assumptions in a local stability proof.

Then prove one exact confluence example and one diameter-stability example.

## Milestone 7: quantitative libraries

Build in this order:

1. signed integers and positive-denominator rationals (reuse existing code where possible);
2. cross-multiplied order and absolute value;
3. powers of two and dyadics;
4. regular-name sample contracts;
5. addition, magnitude bounds, product;
6. apartness-guarded inverse;
7. error-DAG propagation;
8. finite-net coverage and argmin.

## Milestone 8: end-to-end pilot

Select a theorem whose deep producer is already finite and explicit. Required deliverables:

- fixed evaluators;
- local object proofs;
- compiled normalized trace;
- closed `Prf PRAAx` theorem;
- native export;
- `#print axioms` record;
- exact regression tests;
- no unresolved producer hidden in a structure field.

## Non-goals

The compiler does not produce general height bounds, zero-free regions, exact sign selectors, infinite coherent paths, or convergence rates from metastability. Those require additional mathematics or are uniformly impossible.
