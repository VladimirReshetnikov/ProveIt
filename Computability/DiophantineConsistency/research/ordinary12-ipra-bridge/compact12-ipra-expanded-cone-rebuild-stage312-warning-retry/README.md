# Expanded compact/iPRA rebuild: stage 312 exact-warning retry

The rejected attempt emitted six warnings: four unused simp arguments and an
unused/unreachable `all_goals done`. This retry keeps the source unchanged and
accepts only the complete, source-pinned warning log after path normalization.
Five mutation checks reject added, missing and altered warnings, an added
error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 11.694
seconds; the exact warning verifier and final guards passed at 312/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`415705e33108c5c44b9bff0c431c8ec6fccee281b701d04f00e5cf9412adf417`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `9f35461486789868b658e45134731f8a32a36026d0a91916ec288f7b9401dbaf`,
`19b2422b522caaf7827b0819716ab28a89980df0da53f46180fd8cebfb885ee2`,
`19a642ca393e6836a231c71931ca292cc7d4c26f758c35774142409520407b44`,
`8c414bf62e643d32067d8ac1921b561e95146f9a6490291bcd6efaf2b9dd6250`, and
`e4ec62df25846188a1e55a4c0f1cb00b797f934f03b1bc84a56aea8da0e9cee7`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,456,028 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
113 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
