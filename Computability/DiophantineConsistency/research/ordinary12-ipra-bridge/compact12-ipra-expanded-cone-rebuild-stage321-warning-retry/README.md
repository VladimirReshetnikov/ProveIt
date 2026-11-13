# Expanded compact/iPRA rebuild: stage 321 exact-warning retry

The rejected attempt emitted two unused section-variable warnings. This retry
keeps the source unchanged and accepts only the complete, source-pinned
warning log after path normalization. Five mutation checks reject added,
missing and altered warnings, an added error and an added `sorryAx`. This
exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 7.515
seconds; the exact warning verifier and final guards passed at 321/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`f36e434112d2db3945bf438d81a48bade1321782fcc0372a8d087935bde0725f`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `84f71512c01d16bd52d100afdbe757f6e1ea275b01f7319c49403b629f2fb40e`,
`db925c335ce79ed9eceef065778fa32c300b4af9a2f69e3e7f783fba68a8d4de`,
`69a959afd64df98351de3c2d628f4904815a75ed2829cd69a0d0466c92e892ae`,
`4f98238757e1c7a4e1b99474659a7ff5f3900558fc67bc10341afd201b55f197`, and
`187edf9f42df0331e0036c2d097fd91e6c5da7ab149262d54673cfd3b4a1cbe7`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,455,432 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
104 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
