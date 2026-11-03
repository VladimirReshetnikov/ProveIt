# Expanded compact/iPRA rebuild: stage 322 exact-warning retry

The rejected attempt emitted two unused section-variable warnings. This retry
keeps the source unchanged and accepts only the complete, source-pinned
warning log after path normalization. Five mutation checks reject added,
missing and altered warnings, an added error and an added `sorryAx`. This
exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 12.747
seconds; the exact warning verifier and final guards passed at 322/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`fbc4623427745ef4403bf5474195be87aa15c4ece1e01923dab4c87a104f3d22`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `05b0082ea467082b78c9021e1927c1b14fc99fd95a3746c8b00c0e764c8e3125`,
`595451dfa180ef38bc4feb7837434c9c5c3373acc6893aba09ba4131b3cae023`,
`a9dfcb65854e4296500443df81830bcb249a3baa94244122d55405612102b15a`,
`a9f80080fcf961092503166d69bc472a100c7e00fa8b9b81abdbb0e09da0eae9`, and
`5e3669463c92862b2ee70dc7f2e8d01b01867b08f7717b04f3b97a9325ca8233`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,456,116 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
103 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
