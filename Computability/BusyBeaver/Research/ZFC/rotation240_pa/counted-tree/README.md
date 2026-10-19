# Counted decoder tree for the exact 240-state machine

[`CountedTreeRotation240`](../../../../Lean/BusyBeaver/ZFC/CountedTreeRotation240.lean)
proves that a tree with cached subtree sizes is exactly
`ControlCatalogue.annotate TreeRotation240.tree`. Its catalogue has **6,455
entries**. This makes path ranking inexpensive for the forthcoming finite
packed-table check while preserving a proved connection to the canonical
decoder tree.

The generated data has 203 shared nodes. Each node's count and annotation
equations use only the two already proved child equations. A final structural
equality connects the private plain-tree mirror to `TreeRotation240.tree`.
The generator's parsing and numerical counts are not trusted as a substitute
for these Lean proofs.

The [actual check](../../results/w6-counted-tree240-verification.json)
passes three axiom probes and three typed callers with zero warnings. Source
compilation took 2.458 seconds and the audit 0.241 seconds, with default proof
limits and a shared 120-second deadline, one thread and 4,096 MiB. The guard
selects 13 project prerequisites and Init from completed Catalogue and Tree240
checks; it does not rebuild dependencies or replay decoder coverage.

The first source attempt failed because `congrArg₂` was unavailable under the
core imports and opening two namespaces made `CTree` ambiguous. The corrected
generator uses a direct rewrite for addition and opens only `RMBisim.Tree`.
The original generator, failed run, correction and successful run are preserved
in the [history](history.json.gz), together with the source review. That review
initially missed the two elaboration issues; actual compiler evidence controls
the accepted result.

The [publication record](../../results/w6-counted-tree240-publication.json),
[guard](check-v2.py), [audit](Audit.lean) and raw logs retain exact execution
evidence, including historical scratch paths. This unit proves the cached-tree
identity and catalogue length. The packed-row checks and the arithmetic binary
simulation remain open. Attribution follows the canonical TreeRotation240 and
ControlCatalogue sources.
