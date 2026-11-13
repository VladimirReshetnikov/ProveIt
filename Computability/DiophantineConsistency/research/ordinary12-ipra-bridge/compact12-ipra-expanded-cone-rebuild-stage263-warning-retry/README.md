# Expanded compact/iPRA rebuild: stage 263 exact-warning retry

The rejected attempt emitted an `unnecessarySimpa` style warning and an
unused section-instance warning. The instance-bearing lemma is used in this
source and in `LSchema.lean`, so this retry preserves the source and theorem
interfaces. It accepts only the complete, source-pinned warning log after path
normalization. Mutation checks reject added, missing and altered warnings; the
baseline contains no `error:` or `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, prior receipts,
earlier warning baselines and rejected direct dependency guards. It
quarantined the rejected object and recompiled the unchanged source. Lean
exited 0 in 18.679 seconds, the exact warning verifier passed, and final checks
passed at 263/425. Source and dependency guards stayed unchanged. Retry and
quarantined object SHA-256s match:
`7b24b2a930ba755a9d9e9ff2c98200042cb409e801c64eeb07903ad7ae83864d`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `c6633453953825d6d9cd387bcbbffb839c4b61b10dc65a43ffd5bdc4dec4e04d`,
`279a253b4aad516cb42e6a63a087c8d0155a222f02607d6b86f5815995a4366d`,
`a0013896c8f1bd92a651342aa1f1d0c399097b72831a4731147699e81bbeaf71`,
`74bac949c7853b8156a045757fee0eda3180e46707088af9fa28cdfb07252296`, and
`a128c1958a4c138913f29c5fa7f25641c8bdd4dd264f4805448068e301f4cad9`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,428,108 KiB; brief children and overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
162 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
