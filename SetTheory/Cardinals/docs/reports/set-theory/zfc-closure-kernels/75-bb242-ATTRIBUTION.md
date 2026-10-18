# Attribution and provenance

The original compact calculus, program, and machine construction remain
credited to **Mira-Cult**; the cited upstream verification to **Jeff
Ketchersid**; and the compiler framework to **Andrew James Wade**.

The upstream verification reviewed for this report is Jeff's `ZF/m254`
construction at commit
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`. The immediate predecessor is
ProveIt's `candidate-combined243` at commit
`e58338db7545909907e07a7603e8eb88625c527a`. The report contains pinned
source citations and explains which inherited verification stages were
reviewed or rerun.

ProveIt's source program, register permutation, routing, initialization,
QT loop rotation, compensated fold, and incoming research contributions
retain their existing attribution. No personal author is inferred for an
anonymous or unattributed incoming contribution.

This package adds the state-15 branch-borrowing reduction, its direct
whole-tape argument, standalone relative Lean proof, independent checks,
portable discovery tools, and supplementary source/encoding experiments.
The orientation comparison reuses **source 08's exact-word Re-Pair
helpers** and **source 19's complete conjunction layout**, preserving their
recorded attribution. The four-loop rotation likewise builds on the
inherited source program and affine checker.

Inherited notices are included unchanged as `licenses/LICENSE.ProveIt`
and `licenses/LICENSE.Wade`; the byte-identical inherited auditor's
portable directory also contains `LICENSE.ProveIt.txt`. These notices
govern their respective inherited material. This attribution document
does not impose a new license on that material.

Preserve the predecessor identities, distinctions between new and
inherited results, and applicable notices when integrating this package
into `candidate-branchborrow242`. The complete consistency calibration
is inherited ordinary mathematics; the newly compiled Lean result is
the relative binary-machine equivalence.
