# Expanded compact/iPRA rebuild: stage 307 exact-warning retry

The rejected attempt emitted one `unnecessarySimpa` warning. This retry keeps
the source unchanged and accepts only the complete, source-pinned warning log
after path normalization. Five mutation checks reject added, missing and
altered warnings, an added error and an added `sorryAx`. This exception is not
a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 6.169
seconds; the exact warning verifier and final guards passed at 307/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`bdba0367fea01e1c0532bea2d1a0486f763ff150aec86315ac4c8f28ab98a2c6`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `1e0712e98297ea9a6bfa2d73649f9fb92e4020345c2abcf2eb9db8c9a3f218df`,
`592bf9992fb40d541bcbbac519cb5ed341f4d8d9dc7b925f05b7d2a6ef18218b`,
`58fc10967fd146ce94d7feb1082593d2caf3590b7e40f8272573d57501fe7399`,
`25ff6103ff26501fa56a11eaeaa01beb9d76241e70d9e2598d050c59498d3b43`, and
`7b5ac6eb44c1e8856e71a15e2537d9ce5a5056af76836fc34ca950323e2ee470`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,529,628 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
118 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
