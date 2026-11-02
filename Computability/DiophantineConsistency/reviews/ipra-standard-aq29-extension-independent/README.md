# Independent standard-iPRA AQ29 extension-tool review

This review covers the task-specific source-only extension machinery in
[`research/ipra-standard-aq29/extension`](../../research/ipra-standard-aq29/extension/).
It does not cover a completed real AQ29 replay or authenticate inherited
package-transitive and dynamic dependencies.

The production-source fork verifier checks the six planner, freezer, preparer,
builder, comparator and coordinator sources against pinned reviewed reference
versions, allowing only the task's draft/target names, policy path and four
expected declaration names to change. The policy and the checks draft agree
on the ordered reports for `IPRAStandardTheory.provable_iff` and the three
`IPRAStandardAQ29` endpoint declarations. This is an identity and binding
check, not a proof of those declarations.

The preparer requires a pinned matched parent pair and separately observed
successful coordinator exit, rechecks the parent comparator and source graphs,
requires an observed successful freezer, refuses changed parent sources or
new shadowing imports, and creates separate copies of each sibling's seeds.
The builder and comparator recheck declared and reported direct dependencies,
artifact companions, distinct sibling inodes and the four exact target axiom
report names. These checks retain the documented transitive package, dynamic
load and transient-mutation limits. The freezer requires a **current-source**
parent with zero source drift: the currently running v2 parent cannot be
extended with this workflow while its known workspace drift remains. It first
needs a coherently rebuilt current successor, or a separately reviewed
historical-basis workflow.

An independent idle-priority rerun captured exit code 0 for each of seven
controls: planner tests, fork identity, policy binding, preparer tests, freezer
tests, real-Lean adversarial toy extension and real-Lean freezer-to-pair toy.
The captured [receipt](receipt.json), SHA-256
`2dc8edcd1109da856b5da8b3d8ab92e4bb5c7288a361eb8db4ae562c04f921bc`, records
the exact test inputs and outputs; a separate post-run receipt verifier exited
0 and confirmed those source hashes were unchanged. The outer rerun wrapper's
exit field was not retained, so it is not claimed as an observed exit. The
toy scripts remove their internal temporary logs and use a synthetic empty
Foundation provider. They establish neither the real parent pair's completion
nor an actual AQ29 theorem.
