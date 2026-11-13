# Expanded compact/iPRA rebuild: stage 272 exact-warning retry

The rejected attempt emitted three unused section-variable warnings and one
unused simp argument warning. The warned theorems are used later in the source;
this retry preserves their interfaces. It accepts only the complete,
source-pinned warning log after path normalization. Mutation checks reject
added, missing and altered warnings, an added error and an added `sorryAx`.
This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 5.618
seconds; the exact warning verifier and final guards passed at 272/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`1217722f6af7a78773dc27059348be28a0e25d31aee7327a15e3c218011ca909`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `490fc7a2d9acc92b5a6b27663e577eaf328c57ed74fb1353e4553b714155b224`,
`1aac1708f3d503adf706b9f1ed4fd52d86af5cc135718ec72f2b0f07775c0d93`,
`5101c4dfb5bcce0b75c54a4aed364edfd4e36a792ec5e756e09179cc22c6b685`,
`5809bf51a2d9395d5e42210241d3d7890e89b85eedae6452d618f9a28160ffb8`, and
`b6c44daa4f2cad0c5bf2146fc88c8b427a2d0f739a49dbdccddae8bb06b8b626`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,513,928 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
153 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
