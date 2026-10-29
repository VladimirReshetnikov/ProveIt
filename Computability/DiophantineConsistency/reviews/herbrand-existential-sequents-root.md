# Independent replay: Herbrand existential-sequent structure

Lean proves that negating a strict universal-prefix formula yields a formula
with no universal quantifier, and that a cut-free LK derivation whose end
sequent has no universal quantifier contains no universal-rule node. A
separate traversal collects the existential-rule terms of a derivation.
This is structural preparation only: it does not establish that those terms
provide a Herbrand disjunction, handle the free-variable constraints, or prove
PRA witnessing and conservation.

Two separate builds against the independently refreshed syntax provider
`/tmp/pra-universal-syntax-independent-qjrbpk9l/lib` passed both modules with
matching source, object and complete-log hashes. The driver verifies the
frozen parent sources and objects. [Independent driver, state and logs](herbrand-existential-sequents-root-replay/)
and the [author packet](herbrand-existential-sequents-author-replay/) are
retained. Historical failed/warning attempts are evidence only. Foundation,
Mathlib and unchanged local objects remain inherited cache boundaries.

A subsequent upstream merge changed `PRAFormulaParameters.lean` and
`PRAUniversalSyntax.lean`. This receipt authenticates the earlier snapshot;
the affected downstream [source-current replay](pra-parameter-current-root.md)
has since passed.

A later [source-current 43-module refresh](herbrand-all-instantiation-root.md)
rechecked the affected downstream theorem chain after the eleven-prerequisite
upstream refactor.
