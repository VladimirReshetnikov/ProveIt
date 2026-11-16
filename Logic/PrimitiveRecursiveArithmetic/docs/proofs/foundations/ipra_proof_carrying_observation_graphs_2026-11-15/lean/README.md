# Lean artifacts

`ProofCarryingGraph.lean` is the concrete core of the proposed integration.  It
wraps the repository's already checked primitive-recursion invariant theorem
and gives a proof-producing DAG fold whose edges consume and return actual
`Prf PRAAx` derivations.

`BoundedFormulaBlueprint.lean` and `RelationalViabilityBlueprint.lean` state the
next interfaces without asserting unfinished theorems as axioms.  Their full
completion path is in `IMPLEMENTATION_PLAN.md`.

No Lean executable was installed in the artifact environment, so these files
were not elaborated here.  The report does not label them kernel-checked.  The
source is tied to the exact APIs inspected at ProveIt main commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.
