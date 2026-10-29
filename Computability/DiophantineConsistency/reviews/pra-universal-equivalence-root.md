# Independent replay: candidate PRA universal presentation

`PRAUniversalEquivalence.provable_iff` proves, for every sentence of the
explicit primitive-recursive-function language, that the proposed universal
axiom family and the repository's candidate PRA theory have exactly the same
theorems. The direction from universal axioms to candidate PRA proves every
listed axiom; the reverse proves arbitrary-parameter open induction in every
equality model using characteristic functions and bounded-search conditions,
then uses first-order completeness. This theorem concerns these two explicit
theories. It does not prove that the candidate is equivalent to a standard PRA
presentation, or provide PRA witnessing or Π₂ conservation.

A first replay exposed a stale QOrder object in the initial author wrapper.
That failure and the old wrapper are preserved as historical evidence in the
[author packet](pra-universal-equivalence-author-replay/); they were not used
as the corrected proof provider. The author rebuilt the affected wrapper and
manifest. Two separate full replays of its corrected driver, the author's
`/tmp/pra-universal-independent-ewlqkkjl` and root's
`/tmp/pra-universal-independent-m5hxtn5a`, passed all 19 modules and checks
with matching source, object and complete-log hashes. The driver checks 44
local source hashes and unchanged inherited object hashes. Its
[driver, state and logs](pra-universal-equivalence-root-replay/) are retained.
Foundation, Mathlib and unchanged local objects remain inherited cache
boundaries, not a fresh complete transitive rebuild. The axiom checks report
only `propext`, `Classical.choice`, and `Quot.sound`.

A subsequent upstream merge changed `PRAFormulaParameters.lean` and
`PRAUniversalSyntax.lean`. This receipt authenticates the earlier snapshot;
the affected downstream [source-current replay](pra-parameter-current-root.md)
has since passed.

A later [source-current 43-module refresh](herbrand-all-instantiation-root.md)
rechecked the affected downstream theorem chain after the eleven-prerequisite
upstream refactor.
