# Expanded compact/iPRA rebuild: stage 275 exact-warning retry

The rejected attempt emitted four unused section-variable warnings and two
unused simp argument warnings. This retry preserves the source and accepts
only the complete, source-pinned warning log after path normalization. Five
mutation checks reject added, missing and altered warnings, an added error,
and an added `sorryAx`. This exception is not a proof audit.

Two earlier setup attempts stopped before Lean: the first caught a bad
quarantine hash, and the second quarantined the right object but caught an
omitted successful receipt for stage 274. Their evidence is retained. This
runner checks the stage 273–274 receipts, all 425 source pins, selected overlay,
earlier receipts and warning baselines, and rejected direct dependency guards.
It verified the existing rejected-object quarantine at
`/tmp/compact12-ipra-expanded-coherent-20261102/quarantine/stage-0275-rejected.olean`
and rebuilt the unchanged source. Lean exited 0 in 8.946 seconds; the exact
warning verifier and final guards passed at 275/425, with source and direct
dependencies unchanged. Retry and quarantined object SHA-256s both equal
`3a096eb8f79bd3983c0cae8397705572058b2c2bfe70068db7e4da94e59c360a`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `8e66976b169584af3883c1636b64b7baa51395397290d8a1458d315a2ac972fd`,
`3bfb896c2aad415bc0bfcc0ad90705e28e4a16788f33d2b31b7e7973ef44cddb`,
`72c3c834f884ee3d444c96f9db8d23779f3ffdbcc1fab4a329a7211c040ea88d`,
`553a664416f4cd22d8d5c33092dc96ff89ee84a287b34a4cc6bc2605a158e5ec`, and
`8eafa4193c0d42bb6a0e750e8e2d0bcea2dfe887ee8e490edcf4e6b2970e5ca2`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,375,700 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
150 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
