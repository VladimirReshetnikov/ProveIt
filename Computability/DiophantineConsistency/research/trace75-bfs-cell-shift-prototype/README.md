# Trace75 direct-BFS cell-shift client

`Trace75BFSCellShift.graph_cell_shift` adapts the 80-row argument to trace75.
Under the exact symbolic direct-BFS ports and a positive trace75 zero it
proves a common positive repunit length N and a shift s<N satisfying both
`E % 67 = 0` and `(E/67) % (8807*N) = 8807*s`, where
`E = rankNat − 67*(8807*N)`. It identifies independently selected lengths
using their common radix. The author check passed with tool-observed outer
exit 0 and child, Lean and header exits 0. Independent post-audit passed in
`reviews/trace75-bfs-cell-shift-result-independent/`.

The runner checks seven accepted regular client roots, the 1,977-object
fresh union, 80 outside providers and five captured BFS subtrees with 278,
29, 21, 274 and 252 project objects respectively, including companions.
Read-only preflight and 18 policy controls passed. The result
`observations/attempt01/result.json` has SHA-256
`57660aa69e2ecde3b0e10c20f0edb01681f7774d04c80a1c1d7b06e081f7caa3`;
`observations/outer-attempt01/terminal.json` has SHA-256
`48bca5b09f8b1b8759bf2258bb5e21220d567b954d1220ca9644a09165f85944`.
The object `/tmp/trace75-bfs-cellshift-9_fgrs9i/Trace75BFSCellShift.olean`
has SHA-256 `757b5a9f37ede9d67c75b97714f68d2c5c2c48c48cdd8845145ccadb82e047b8`.
Historical unrebuilt-source, package/dynamic
ancestry and external coefficient-file binding remain outside this check;
this is not a machine-halt or iPRA claim.
