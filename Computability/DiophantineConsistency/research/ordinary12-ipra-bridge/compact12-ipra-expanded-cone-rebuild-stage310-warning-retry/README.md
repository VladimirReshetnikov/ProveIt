# Expanded compact/iPRA rebuild: stage 310 exact-warning retry

The rejected attempt emitted three warnings: an unused and unreachable
`(exfalso; omega)` tactic and an unused `done`. This retry keeps the source
unchanged and accepts only the complete, source-pinned warning log after path
normalization. Five mutation checks reject added, missing and altered warnings,
an added error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 12.518
seconds; the exact warning verifier and final guards passed at 310/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`7a8d49aa7939dc3c3bbdb282c7bd1c858841b48a7b94268657b958559636df2e`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `a29f07c4d478034239d45e1cf9e002aa12cea02fb399c637e72c0701d2e015ba`,
`31ac86cc09d9b2376acd039c6dbc2819c3d67bdbb3efbbbdd7b66e7e4a8582ba`,
`ad7050a6d57fa2d9b1846bd28e563f7fca2692fbd713b97f26236f58f78366e1`,
`fac1a5aa52dbac36677ce9d5277bd3e130fbd72247e0a75aaeedb5f24431e304`, and
`a7fa3991b1833b7b166ae122ca07fea5288fd768832baf85c264ca017d4e1717`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,490,308 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
115 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
