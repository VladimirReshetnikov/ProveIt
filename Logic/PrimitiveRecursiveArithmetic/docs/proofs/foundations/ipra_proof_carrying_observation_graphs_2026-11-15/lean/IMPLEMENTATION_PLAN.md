# Lean implementation plan

## Target environment

Integrate into the existing Lake library under namespace
`LeanProofs.ConciseIPRA.PCOG`.  The inspected repository exposes:

- `ConciseIPRA.Syntax`: scoped terms/formulas and substitution;
- `ConciseIPRA.Deduction`: `Prf`, weakening, substitution, simultaneous cut,
  equality transport;
- `ConciseIPRA.PR`: `PR`, `PTm`, `PRAAx`, defining-equation lemmas and
  `PRA.qfInd`;
- the checked packet file `ipra_local_global/lean/ObjectIteration.lean`, whose
  `primitiveRecursionInvariant` and `primitiveRecursionAt` should be moved,
  without its frozen kernel copy, to `ConciseIPRA.FiniteTrace`;
- the checked packet file `ipra_stable_observables/lean/ObjectObservation.lean`,
  whose five derivation combinators should be moved to
  `ConciseIPRA.ObservableGlue`.

The archive does not claim that these moves have already been made.

## Dependency-ordered milestones

1. **Repository integration of the checked trace rule.** Replace
   `ObjectKernel` by imports from `ConciseIPRA.PR`; compile
   `primitiveRecursionInvariant`, `primitiveRecursionAt`, and the counting
   example.  Run `#print axioms` on all three.
2. **Core graph module.** Compile `ProofCarryingGraph.lean`.  This layer is
   only proof-term composition.  Expected repairs are import names and minor
   list-membership syntax, not mathematical lemmas.
3. **Boolean library.** Add concrete PR symbols for Boolean equality,
   conjunction, disjunction and negation; prove defining equations with
   `PRA.comp`, `PRA.precZero`, `PRA.precSucc`, and equality combinators.
4. **Bounded folds.** Define `allBelow`, `anyBelow`, and `leastBelow` by
   primitive recursion.  Prove reflection/minimality by `PRA.qfInd`.
5. **Term-to-symbol adapter.** Integrate the checked
   `TermCompiler.symbol_correct` and `transport_equation` declarations from
   `ipra_resources_and_elimination_2026-11-15`.  This avoids re-proving a
   compiler for fixed term syntax.
6. **Strictly bounded formula compiler.** Implement host recursion on `BForm`.
   Every recursive call returns a `BoolReflection`; bounded binders invoke the
   fold theorems.  There is no numeric code for an arbitrary PR program.
7. **Tuple and table coding.** Use one fixed pairing family and prove read/write
   equations.  Generate fixed-length tables by primitive recursion.  Keep the
   dimension external and fixed for each theorem.
8. **Backward demand pass.** Compile a fixed reverse topological list to PR
   syntax.  Prove its table equations.  Reuse
   `DemandCompiler.object_backward_zero` and
   `DemandCompiler.object_backward_succ` where possible.
9. **Forward run.** Generate a `TracePackage` whose invariant states that every
   completed row satisfies its local contract and every pending input has the
   computed demand.  Prove base and step by a finite dispatch lemma over the
   fixed node list.
10. **Relational viability.** Implement reverse-time `W`; prove
    `viable_iff_path` and least-path correctness using the bounded folds.
11. **Stable observation layer.** Integrate `ObservableGlue`; formalize
    diameter and gap-collapse inequalities over coded rationals.
12. **End-to-end benchmark.** Formalize the exact bisection graph for
    `y^3+y=x` on `0<x<=2`, including the guarded reciprocal node.  The final
    theorem should literally have type `Prf PRAAx [] (...)`.

## Audit discipline

For each milestone:

- run the root Lake build;
- prohibit `sorry`, new `axiom`, `Classical.choice`, and semantic
  truth-to-provability functions in the dependency closure;
- print axioms of the final `Prf PRAAx` declarations;
- retain a theorem ledger distinguishing definitions of goals from proofs;
- test the final theorem's type, not merely a host `Prop` analogue.
