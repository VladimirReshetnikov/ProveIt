# Dependency-ordered Lean formalization roadmap

This roadmap is designed to prevent the common failure mode in which a large
semantic development is completed before anyone checks that its conclusions
can inhabit the repository's deep embedding.

## Phase 0 - interface compilation

1. Place `KernelCompiler.lean` and `ArithmeticInterface.lean` beside a checkout
   where `ConciseIPRA.PR` and `ConciseIPRA.NativeBiInterpretation` resolve.
2. Compile with Lean 4.32.0 and the pinned Mathlib revision.
3. Run the three `#print axioms` commands at the end of `KernelCompiler.lean`.
4. Repair only API mismatches.  Do not replace a target by `True`, a host
   equality, or an unproved axiom.

Expected outcome: a small trusted generic layer whose theorems conclude
`Prf PRAAx`.

## Phase 1 - fixed coding library

Define, as concrete `PR` codes rather than a universal evaluator:

- Boolean negation/conjunction/disjunction and equality/order tests;
- pairing and bounded tuple projections;
- bounded lists and tables: length, get-with-default, update, append, fold;
- signed integers and normalized rational pairs;
- resource vectors containing precision, fuel, height, support, and branch
  budgets.

For every code prove:

1. its defining equation as a `Prf PRAAx` theorem;
2. a quantifier-free graph formula;
3. substitution/congruence helpers;
4. bounds needed to keep subsequent search primitive recursive.

This is the first genuinely arithmetic block.  Its statements should be small
and independently reusable.

## Phase 2 - Boolean reflection and bounded folds

For each Boolean checker `b`, define

```lean
checked b args := app b args = 1
```

and prove object derivations for:

- correctness of `allBelow`, `anyBelow`, and bounded minimum;
- table lookup/update equations;
- a fold invariant relating the accumulator after stage `i` to the prefix
  already inspected.

All induction formulas must be visibly quantifier-free.  Existentials are
introduced only after a concrete witness term has been computed.

## Phase 3 - trace compiler instance

Represent a trace state by one natural code containing:

- current stage;
- current domain state;
- frozen input parameters;
- current resource vector;
- accumulated certificate fragments.

Construct the fixed PR functions `init`, `step`, and `run = prec init step`.
Instantiate `TraceObligations` with:

- a QF invariant saying the coded state is the result of the first `i` steps
  and every local checker has accepted;
- a base derivation from the defining equations;
- a step derivation using one local checker-soundness theorem;
- a finish derivation extracting the requested certificate.

`TraceObligations.compile` then supplies the final implication theorem.

## Phase 4 - proof-carrying DAG generation

Use `code/generate_lean_schedule.py` as a conservative generator:

1. topologically sort the fixed graph outside iPRA;
2. reject forward references and duplicate nodes;
3. emit formula parameters and local proof arguments;
4. compose them only through `ProofBuild.step`/`stepFrom`;
5. retrieve the final theorem with `ProofBuild.get`.

The generator is not trusted: Lean checks the emitted proof term.  Minimal
parent lists can be handled by `stepFrom`; the included example uses all prior
nodes for a compact skeleton.

## Phase 5 - bounded relational paths

Encode layers as bounded tables and compatibility as a fixed Boolean code.
Implement, by reverse bounded recursion, the viability table

```text
V(last,x) = candidate(last,x)
V(i,x)    = candidate(i,x) and exists y<bound(i+1), compat(i,x,y) and V(i+1,y).
```

Prove by QF induction on the reverse-stage counter:

- soundness: marked entries extend to a path;
- completeness: every extendible entry is marked;
- least viable successor exists whenever the current entry is marked.

The bounded-minimum code then produces a canonical path, after which
`WitnessObligations.compile` exports any required existential.

## Phase 6 - stable observations and exactness

For approximate, quotient, or tie-dependent constructions, formalize a
comparison theorem between any two valid certificates.  Feed its embedded
proof to `RelationalObservationObligations`.

Only when a discrete output is required, add an explicit separation theorem:

- a nonzero lower bound;
- an isolated-root radius;
- a spectral gap;
- a uniqueness radius;
- a finite margin between competing scores.

Instantiate `ExactnessObligations`; without the gap, retain the relational or
approximate conclusion.

## Phase 7 - domain adapters

### Algebra and combinatorics

Use finite tables, normalization traces, and direct checkers.  Most results
should terminate at Phase 4 or 5.

### Analysis and differential equations

Use rational names with explicit precision transformers.  For finite-use
clients, a metastable finite-window contract may replace an unavailable global
rate.  Inverses and branch selection are guarded by apartness/gaps.

### Topology

Represent finite complexes, subdivisions, chains, and carrier maps by bounded
codes.  Avoid coherent geometric representatives: prove chain-level
comparison or homotopy and erase tie choices through stable homology data.

### Algebraic geometry

Separate finite algebra (Macaulay matrices, Gröbner-style reductions, resultants,
finite chart checks) from global arithmetic height bounds.  The former enters
trace/DAG obligations; the latter is a `BoundaryObligations` field unless an
explicit primitive-recursive producer is supplied.

### Number theory

Keep ineffectivity visible.  A theorem depending on an ineffective exceptional
zero bound, height bound, or finiteness cutoff is not a producer.  It may still
be formalized conditionally via the boundary interface.

## Phase 8 - auditing standard

For every packet record:

- exact ProveIt commit and source hashes;
- theorem statements and whether they conclude `Prf PRAAx`;
- all `sorry`, `axiom`, `Classical.choice`, and quotient dependencies;
- which algorithms are only host-level tests;
- which bounds/moduli/gaps are proved, assumed, or absent;
- `#print axioms` output for final object theorems.

A packet is complete only when its claimed object theorem compiles and its
boundary assumptions match the mathematical statement advertised to readers.
