# Expanded compact/iPRA rebuild: stage 371 exact-warning retry

The rejected attempt emitted two unused section-variable warnings. The warned
lemmas are used later in the same source. This retry keeps the source
unchanged and accepts only the complete, source-pinned warning log after path
normalization. Five mutation checks reject added, missing and altered warnings,
an added error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 47.031
seconds; the exact warning verifier and final guards passed at 371/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`20f422201ad460a7e820ff050faaffc0b8317fefa941a710041225de8b64051f`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `9d45176105a1587ef37d7cf31a4ae70a305c15f6469afc5765e82ba297353a64`,
`c0ee68210076c7dba9e3f4fb0effd07fe58aa200d2a9cc77d023c1c815571276`,
`cbd0be31bdf54249af3cd2b66c45d0ed82b4e88e3d7fdd6fd50acdec6db2998a`,
`969a7cf0947323ba7bbc80f7486d9d954ba0811cea7134d69f5bf495ccad0ea4`, and
`89f76365adf1d22bf4c1da37834290e1f32c900765bf660198c94b7c1a28fee5`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,369,444 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
54 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
