# Expanded compact/iPRA rebuild: stage 268 exact-warning retry

The rejected attempt emitted 14 unused simp argument linter warnings and no
`error:` or `sorryAx`. This retry preserves the source and accepts only the
complete, source-pinned warning log after path normalization; it does not
suppress warnings. Mutation checks reject added, missing and altered warnings,
an added error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, plus the rejected attempt's dependency guards. It
quarantined the rejected object and rebuilt the unchanged source. Lean exited
0 in 12.790 seconds; the exact warning verifier and final guards passed at
268/425, with source and direct dependencies unchanged. Retry and quarantined
object SHA-256s both equal
`c77acd4034ea48878c4acde8a6282e346dfaf063875d8b27b476735f501e89b2`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `8dc35524b4bee93514673da1ea658a804f78ff5b16ea8cdfbf6e0a461fbebb0e`,
`00bff6d23e5785a9c66b1a234a64b56dd682d0e0f3eda3e4daefa2b2ed97c016`,
`af050e63c91d13e3e7983dd1d41541a2bd07d5f85f7bfafc2b9d6fefbea233d0`,
`a0c5ed7999834c026c21991481c21d85d5ea377be8bfb4a73d0a70af4f02f3d9`, and
`d1e8817ee880cd4e339077ce5024363f52ca37433ab728a6c1c18b00537fdcca`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,461,080 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
157 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
