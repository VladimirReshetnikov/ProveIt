# Expanded compact/iPRA rebuild: stage 367 exact-warning retry

The rejected attempt emitted three unused binder warnings (`k`, `k`, `hF`).
The affected lemmas are used in this source and other modules. This retry
keeps the source unchanged and accepts only the complete, source-pinned
warning log after path normalization. Five mutation checks reject added,
missing and altered warnings, an added error and an added `sorryAx`. This
exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 13.970
seconds; the exact warning verifier and final guards passed at 367/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`8ec6803300a5009ddf341e951f24316016186bd0a37d1a7ffa53b7890449014f`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `1220da7c83aa7d86de81805fd26035ffee7bf9c8cc6eef08c98e30a6b6c7e66b`,
`65911551b9827db3ac848194ab2436931830c1ea98daa8a018304c535e5a58c6`,
`2c0502cc2cc152ebddcecea78fbcf28f6c866e5bf86461541429e578ae4fea5f`,
`9b1d52354650f7410aa5e7a15de17c56a9d7269d330f6ecd48b4bbf155845863`, and
`1bb53ea0b6625ad2f68dd0cc77094d425fdae1b6f5f971b826c81e6f0ee222e9`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,441,660 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
58 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
