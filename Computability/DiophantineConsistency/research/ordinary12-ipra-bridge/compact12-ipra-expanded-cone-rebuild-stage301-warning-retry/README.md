# Expanded compact/iPRA rebuild: stage 301 exact-warning retry

The rejected attempt emitted one broad simp discrimination-tree key warning
and six unused simp argument warnings. This retry keeps the source unchanged
and accepts only the complete, source-pinned seven-warning log after path
normalization; it does not suppress the broad simp warning. Five mutation
checks reject added, missing and altered warnings, an added error and an added
`sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and the rejected direct dependency guards. It
quarantined the rejected object and rebuilt the unchanged source. Lean exited
0 in 28.772 seconds; the exact warning verifier and final guards passed at
301/425, with source and direct dependencies unchanged. The retry and
quarantined object SHA-256s both equal
`0bba9aba3ebbd6a5847f62c7d6cbf54cbf759c611c437f6e3bbfd558956b52eb`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `071db8229f82d2d7340f7f7b69de503f7834d2c9fd5f7b890e702bcd80e1a255`,
`7d126379f2b85f4843c3971bc1175d63f2dc8a46ec570d9e47f8429ed13b3f5f`,
`b566b1b13506219eab779caa58a23953a27cc07159d002bce1b475be247861c8`,
`07ad10de08cd8a7e9a161fbc2ce2e4ff136b5e4ea1f496cc0a23435071bd305b`, and
`653c2dc346fd9f8c82d9545efefdd877db3eb535a0c1707b4b18724ff1f74fe4`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,417,796 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
124 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
