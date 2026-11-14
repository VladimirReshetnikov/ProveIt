# Independent source audit for the 195-state machine

`audit.py` verifies that the primary 195-state construction has the exact
same 190-token axiom word and the exact same 3,673-site branch-resolved
register program as the supplied separated-diagonal 196-state parent.
All six parameter permutations are identity. There is no logical change.

Run `python3 audit.py` using Python 3.10 or later. It needs only the standard
library and the vendored files in this directory. The audit also checks
the complete binary tables, graph reachability, six simultaneous reader
folds, two independent source resolvers, the exact blank startup of both
machines, and their complete symbolic primitive-runtime cases. It writes
`receipt.json`.

The source-to-tape mathematical theorem and its internal PA finite-trace
argument are in `preservation.tex`. It explicitly states the inherited
arbitrary-register block contracts and the parent calculus calibration.
The resulting PA consistency biconditional is an ordinary mathematical
preservation argument; the package does not claim a newly exported Lean
kernel theorem for that endpoint.

Source provenance: ProveIt commit
`906367250a7f96c923147b10df392294bced7be5`; separated-diagonal parent from
`docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip`.
The new grammar is the root search's `exact.best.grammar.json`, compiled
with the original PA196 fixed control. `reference` preserves the pinned
upstream PA196 program, conjugacy, literal table and original AX word.
The imported source graph resolver comes from the pinned K225/K226
verification utilities. Original license notices are retained.
