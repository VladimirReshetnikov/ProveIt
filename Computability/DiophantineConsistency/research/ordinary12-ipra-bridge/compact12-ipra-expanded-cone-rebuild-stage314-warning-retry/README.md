# Expanded compact/iPRA rebuild: stage 314 exact-warning retry

The rejected attempt emitted three warnings: two unused simp arguments and
one unnecessary `simpa`. This retry keeps the source unchanged and accepts
only the complete, source-pinned warning log after path normalization. Five
mutation checks reject added, missing and altered warnings, an added error and
an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 13.996
seconds; the exact warning verifier and final guards passed at 314/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`4bc3f4677aaf7b8f9110b491bbac6f0df5808a59d8eab57b40235145903d97d9`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `3b6161234776819955bc109d43fc3e3b2df96d267ed9e2ac3ba5e68fca1f4f78`,
`5db5bd5ba54142edfb041c55ac6375a1646dc980e31732c55e9ebc8efb816257`,
`9209c94e607bf7566d7cf385cc7b8390daa22e082327d1541ca38daf51cb2f60`,
`6be60bc8eb0b0208f10869272b40ab37eecedd699fd7f70cfea98913f62d0702`, and
`0d569a131b05f2a2a2071ee72c05261103ab6c058c85a20dd01f98fd61ab263f`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,456,496 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
111 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
