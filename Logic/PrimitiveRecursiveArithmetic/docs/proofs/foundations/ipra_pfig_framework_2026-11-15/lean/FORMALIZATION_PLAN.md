# PFIG Lean formalization plan

## Upstream dependency

Pin ProveIt commit `34816faca8aa605999290b41d26210753b5c3b38` or a later explicitly audited commit. Reuse the canonical `ConciseIPRA` syntax, derivability, primitive-recursive term, and iPRA axiom modules. Do not copy `ObjectKernel.lean` snapshots into the new shared library.

## Milestone 0: consolidate checked object combinators

1. Move/import `primitiveRecursionInvariant` and `primitiveRecursionAt` from the local-global packet into a shared namespace.
2. Move/import `ExactContract`, `LoopCertificate`, and stable-observer lemmas.
3. Add `#print axioms` for all public theorems.
4. Compile one existing identity-iteration example.

Exit criterion: no `sorry`; conclusions are actual `Prf PRAAx` values.

## Milestone 1: Boolean reflection

Implement fixed PR symbols for Boolean not/and/or, equality, order, pair projections, table indexing, and bounded folds. Prove:

- Boolean range (`b = 0 ∨ b = 1`);
- reflection for connectives;
- reflection of bounded `All` and `Any` folds;
- syntax-directed Booleanization of QF formulas;
- equality decidability and double-negation stability.

Induction matrices must be literal equations or QF formulas. Quantified specifications are introduced only after reflection.

## Milestone 2: least bounded search

Compile the `(found,witness)` state. Prove validity and minimality from a nonempty bounded predicate. Test on least divisor, least table entry, and bounded argmin.

## Milestone 3: viability

Use rectangular tables with row bound `max_{i≤H} B(i)`. Run reverse recursion over `(H-i,a)`. Prove:

- table recurrence reflection;
- viability iff finite compatible path;
- least viable start and successor;
- path checker correctness;
- product-cloud amalgamation.

First prove semantic list theorems, then object reflection. Keep statuses separate.

## Milestone 4: shrinking and metrics

Build exact signed-integer/rational-code inequalities, finite triangle sums, and geometric tail budgets. Prove adjacent coherence from a certified predecessor pair, then regular-name extraction. Avoid Mathlib real-number semantics in the object theorem.

## Milestone 5: generated two-pass PFIG

Generate one specialized theorem file for a concrete graph:

1. reverse scalar demand loop;
2. forward exact/search/viability loop;
3. terminal stable observer;
4. final `Prf PRAAx` theorem.

Recommended example: bisection/monotone search for the unique real root of `y^3 + y = x`, using rational interval codes and a direct separation/monotonicity proof.

## Milestone 6: negative transfer

Complete the targets in `NegativeTransferBlueprint.lean`:

- equality stability;
- stability of all translated formulas;
- induction over `Prf ClassicalPRAAx`;
- QF recovery using Booleanization;
- retained equivalence;
- retained transfer and source-theory lifting.

Isolate the `orE` and `exE` proof patterns as helper lemmas to reduce binder complexity.

## Milestone 7: finite gluing and height/list

Implement bounded tuple construction, overlap checking, and stable global extraction. Implement bounded-height enumeration and duplicate elimination by a decidable equivalence relation.

## Milestone 8: internal graph compiler

Only after several generated examples compile, define a typed PFIG AST and prove the elaborator sound. The AST is metasyntax elaborated to fixed `PR` terms; do not define or assume an object-level universal evaluator.

## Variable order conventions

- loop invariant: `state, time, parameters`;
- candidate relation: `candidate, precision, parameters`;
- edge relation: `next, current, precision, parameters`;
- metric relation: `left, right, tolerance, parameters`.

Create named instantiation helpers and prove substitution lemmas once. Never build these `Fin.cases` terms ad hoc in application modules.

## Verification gates

A claim is object-complete only if:

1. the object formula is defined;
2. the public theorem concludes `Prf PRAAx`;
3. the file has no `sorry` or added arithmetic axioms;
4. `#print axioms` is recorded;
5. the theorem is included in a clean build from the pinned commit;
6. any native-calculus transfer is checked after the ordinary derivation.
