# Expanded compact/iPRA rebuild: stage 414 exact-warning retry

The rejected attempt emitted three unused section-variable warnings and one
unused simp argument warning. The warned theorems are used later in the same
source. This retry keeps the source unchanged and accepts only the complete,
source-pinned warning log after path normalization. Five mutation checks reject
added, missing and altered warnings, an added error and an added `sorryAx`.
This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 6.103
seconds; the exact warning verifier and final guards passed at 414/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`373896711055c838dc22a84440b934dcb0938b44a87f4eca4ec9e7321856844d`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `b52a4c456a852af54336afba2bcf61874866644b8f4355478a53f8fa1c8c590e`,
`d8fa78030a6cbc3a56b34e9f0e2247d44d53a35c51799d3a4904fd8ab1bf0f98`,
`beb1e698c8e3c77b2955fb918d7823a01c3063b133e9a9bccdf0e216f22723aa`,
`f3ec6247b746e1c092a4242f145bb6202e6c9267d8e419aecfaaf71f8be3f2f9`, and
`21119cd5659751cf3c1c9a8cbe08bebe4308e08d6b5ef34c23985444a7e610f2`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,428,628 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
11 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated. `QSchema` may encounter the known newer-helper
source/provider mismatch.
