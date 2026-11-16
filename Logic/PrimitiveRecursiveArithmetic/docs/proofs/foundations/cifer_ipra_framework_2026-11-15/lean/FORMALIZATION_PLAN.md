# CIFER Lean formalization plan

## Formal endpoint

A successful application must end with a declaration whose type is literally

```lean
[] ⊢[PRAAx] goal
```

or, after export through the checked bridge,

```lean
NPrf [] (NFm.ofPRA goal)
```

A host theorem about `Nat`, an executable Boolean checker, or a Mathlib semantic theorem is not by itself an iPRA derivation.

## Upstream API used

The outline targets the current `LeanProofs.ConciseIPRA` namespace:

- `PR`, `PTm`, and `PRAAx` from `ConciseIPRA.PR`;
- `Prf`, `Prf.trans`, substitution and weakening from `ConciseIPRA.Deduction`;
- `PRA.qfInd` for quantifier-free induction;
- `pra_iff_native` from `ConciseIPRA.NativeBiInterpretation`.

## Dependency-ordered milestones

### M0. Elaborate the composition core

Place `CIFER/` under the root Lean source tree, add the import to the workspace, and build `CIFER.ObjectCompiler`. Resolve only API drift; do not weaken the endpoint types. Run `#print axioms` on:

- `ResidualBuild.compileThreeResidual`;
- `loop`;
- `stableObservable`.

Expected dependencies are those already inherited from the root library; the module must introduce no axiom and no `sorry`.

### M1. Scoped formula utilities

Add reusable constructors for:

- numerals, Boolean values and Boolean connectives;
- bounded comparison and bounded quantifier folds;
- tuple/list coding, projection, update and bounded membership;
- a formula expressing that a checker returns `1`.

Prove `Fm.QF` lemmas for every invariant constructor. Keep syntax constructors separate from semantic evaluators.

### M2. Boolean reflection

For each fixed quantifier-free formula `A`, construct a primitive-recursive Boolean term `b_A` and embedded derivations of

```text
A -> b_A = 1,
 b_A = 1 -> A.
```

Proceed by host recursion on the fixed formula. Equality reflection uses the existing arithmetic comparison library. Conjunction, disjunction and implication use Boolean truth tables. Strictly bounded quantifiers become finite folds and are proved by `PRA.qfInd`.

### M3. Bounded search and enumeration

Define the search state `(found, least)` and prove its quantifier-free invariant. Derive:

- success implies the returned code satisfies the predicate;
- minimality below the returned code;
- failure implies no code below the bound satisfies it;
- filtering a bounded code interval gives a complete list.

All loops use `CIFER.loop`; existential conclusions use `existsFromWitness`.

### M4. Residual graph compiler

Prove `reachable_correct` and `residual_characterization` in `ResidualGraph.lean`. Then enrich every graph node with:

- its object formula;
- a list of dependency indices;
- an actual local derivation from those dependency formulas and the permanent context.

Fold in topological order with `ResidualBuild.stepFrom`. The output theorem should state that the target is derivable from exactly the dependency-normal residual boundary context. This is syntactic normalization, not undecidable logical minimization.

### M5. Capped demand closure

Complete the rank argument in `DemandClosure.lean`. Compile a fixed-dimensional vector into one coded natural state. The induction invariant says:

1. every coordinate is below its cap;
2. the trace is inflationary;
3. the current state is the declared iterate;
4. once stable, it stays stable.

Use the explicit fuel `rank cap - rank seed + 1`.

### M6. Finite relational viability

Implement backward viability over encoded finite levels. Prove `viable_iff_path` by reverse induction on the horizon, and construct the least viable path by bounded search. Add exact stable-observer elimination and rational diameter estimates. Do not introduce a choice function on ideal infinite objects.

### M7. Query-local specialization

Define a host compiler that accepts a *fixed* graph description and generates concrete `PR` syntax. Do not encode a universal evaluator in the object theory. Generated names should include the graph hash and node index so source and object statements can be audited.

### M8. End-to-end benchmark

Formalize exact rational bisection for `y^3 + y = x`:

- signed rational coding and cross-multiplied order;
- initial bracket `[-(|x|+1), |x|+1]`;
- midpoint update;
- monotonicity of `y^3+y` by the factorization
  `(b^3+b)-(a^3+a)=(b-a)(a^2+ab+b^2+1)`;
- bracket invariant and width `2M/2^s`;
- choose primitive-recursive fuel from the requested dyadic precision.

The benchmark must produce a closed `Prf PRAAx` derivation, not merely a native Lean theorem.

### M9. Domain adapters

Only after the benchmark closes, add adapters for:

- height bound -> complete Diophantine list;
- finite root clusters -> collision-stable observables;
- rational finite nets -> extrema and uniform estimates;
- finite simplicial carriers -> induced chain maps;
- supplied effective analytic constants -> finite prime-sum inequalities.

Each adapter has a boundary theorem and a verifier theorem. The boundary remains visible until an actual producer derivation is supplied.

## Recommended review gates

At every milestone:

1. build with the pinned toolchain;
2. search for `sorry`, `axiom`, and `unsafe` in the new modules;
3. run `#print axioms` on the public endpoint;
4. inspect the endpoint type for `Prf PRAAx` or `NPrf`;
5. regenerate the source audit and graph manifest;
6. keep finite executable tests separate from proof status.
