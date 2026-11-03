# Expanded compact/iPRA rebuild: stage 369 exact-warning retry

The rejected attempt emitted six warnings: two unused section-variable
warnings, two unused binders and two unused simp arguments. This retry keeps
the source unchanged and accepts only the complete, source-pinned warning log
after path normalization. Five mutation checks reject added, missing and
altered warnings, an added error and an added `sorryAx`. This exception is not
a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 10.895
seconds; the exact warning verifier and final guards passed at 369/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`ab4dadf47e5ba8c7b8acf10b4d45c44da949b96e02cc38b21e9ac6a085aebe73`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `7779d0b6834186b47068dcd74b0867e126f90df2eba4f46d98f826aef0a69a9f`,
`ba1e627ebdc967f17ba5645893e7623f6fac8aec5cc5e280f9353f19377267d3`,
`a3b8a838ac1219f48e392d963c44e95db4e3c5810efae50c0df2653ca743fe48`,
`f9fa60854c16dddf8218094b216662c74881dea540d8769f685522bc527575bd`, and
`99224581a1e1c4b651e0c18079349cb673b32cf16cd040c2230d309a18f60d8e`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,394,656 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
56 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
