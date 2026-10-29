# Finite side-list normalization

For a finite list of supplied packed strict-prenex trees, Lean constructs one
bounded tuple matrix and actual PA-minus rule proofs in both directions
between its block and the exact `ParsonsStructure.disjoin` of the input
formulas. The empty list corresponds to falsity. This is a proof-output
adapter and assumes a tree descriptor for each side formula; it is not a
height-preserving source-derivation adapter or a general Π₂ normalizer.

Two isolated builds against the independently replayed mixed-tree provider
`/tmp/parsons-prenex-tree-independent-chn_ko1q/lib` matched source, object and
complete-log hashes. The driver verifies frozen local providers. The [independent
driver and logs](parsons-prenex-list-root-replay/) and [author packet](parsons-prenex-list-author-replay/)
are retained. Foundation, Mathlib and completeness objects remain inherited
boundaries.
