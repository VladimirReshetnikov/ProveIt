# Trace75 direct-BFS aligned-shift client

`Trace75BFSAlignedShift.graph_aligned_shift` adapts the 80-row argument to trace75.
Under the exact symbolic direct-BFS ports and a positive trace75 zero it
proves a common positive repunit length, carry input, and temporal exponent
`(rankNat − 67*(8807*N)) % 67 = 0`. It uses the audited phase-parity and
occupied-anchor results and identifies separately selected lengths through
their common radix. The author check passed with tool-observed outer exit 0
and child, Lean and header exits 0. Independent post-audit passed in
`reviews/trace75-bfs-aligned-shift-result-independent/`.

The runner checks six accepted regular client roots, the 1,977-object fresh
union, 80 outside providers and captured BFS subtrees for `DirectBFSCarryRoom`,
`FractionalAnchorConflict` and `OccupiedNamedSlots` (21, 274 and 252 project
objects, respectively), including companions. Read-only preflight and 18
policy controls passed. `observations/attempt01/result.json` has SHA-256
`76788e416a7ed045716de97e103d2346cdee29f306acfcbb49447e5a834d33da`;
`observations/outer-attempt01/terminal.json` has SHA-256
`953c46e5cafe93266535b854948af27535999bdac7510c614f655561d7fa3f9f`.
The object `/tmp/trace75-bfs-alignedshift-64rdplmm/Trace75BFSAlignedShift.olean`
has SHA-256 `e031954c734ca8bbecf74a134acb9bfe2bdeeccebe2550f1a79e85dda76deb64`.
Historical
unrebuilt-source, package/dynamic ancestry and external coefficient-file
binding remain outside this check; this is not a machine-halt or iPRA claim.
