# KIFC-S Lean formalization plan

Target snapshot: `7fa3ba48e8f62e8018ed954faaa48b908217eaf1`.

The artifact runtime did not contain Lean.  The source files are therefore not
claimed to be compiled.  Complete the work in the following dependency order.

## Phase 1 - contract core

Place `KIFCS/OpenContract.lean` in the root workspace and compile it against
`ConciseIPRA.NativeBiInterpretation`.

Exit criteria:

- `Contract.ofPrf`, `toPrf`, `iff_prf`, `trans`, `subst`, and `iff_native`
  compile;
- no compatibility shim imports an application project;
- `#print axioms` reports only the metatheoretic axioms already present in the
  ConciseIPRA library.

## Phase 2 - normalized trace

Compile `NormalizedTrace.lean`.  Repair only namespace/API drift; keep the
base, step, and finish fields in the exact forms consumed by `PRA.qfInd`.
Add a tiny counter or finite-sum trace as a test.

Exit: a theorem of type `[] ⊢[PRAAx] ResultFm T` and its native corollary.

## Phase 3 - fixed Boolean reflection

Implement `Reflected` constructors for equality, order, conjunction,
disjunction, and negation.  Reuse the existing monus/order and bounded-search
modules.  Add bounded `allB` and `anyB` folds with range and reflection
contracts.

Exit: reflection of a nested bounded formula with an axiom audit.

## Phase 4 - two-sided strategies

Implement the fixed-syntax metalevel compiler described in
`BoundedStrategyBlueprint.lean`.  Generate truth and falsity certificate
layouts, checkers, canonical constructors, and the decision contract.

Exit: one `forall-exists-forall` theorem with both certificate directions.

## Phase 5 - query graph

Implement metadata validation, backward reachability, stable boundary
normalization, topological sorting, and contract composition.  The generator
must reject logical cycles unless they have already been collapsed to a
certified trace/descent node.

Exit: generated modules for `examples/residual_height_graph.json` and
`examples/dead_end_relation.json`, with printed residual frontiers.

## Phase 6 - coherence library

Formalize finite viability in the object theory, least viable paths through
checked search, exact and diameter-stable observers, explicit extension
systems, rational triangle sums, and finite-tail regularity.

Exit: one Level-I example that avoids selecting a branch, one Level-II path
example, and one Level-III regular-name theorem.

## Phase 7 - open Foundation bridge

Follow `BridgeBlueprint.lean` and the repository `UNIFICATION-PLAN.md`.
First prove translation/substitution and round-trip simp lemmas, then recurse
on derivations.  Test a two-hypothesis sequent, an induction formula with a
parameter under a binder, and existential elimination with a fresh variable.

Exit: a public open-contract transport theorem in both directions.

## Phase 8 - application adoption

Recompile one finite-analysis packet and one Diophantine enumeration packet
through KIFC-S.  Keep previous public theorem names as checked corollaries.
Record exact residual assumptions and generated-source provenance.
