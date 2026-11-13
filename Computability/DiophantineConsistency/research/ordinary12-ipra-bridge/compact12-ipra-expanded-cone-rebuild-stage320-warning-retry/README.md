# Expanded compact/iPRA rebuild: stage 320 exact-warning retry

The rejected attempt emitted one unused simp argument warning. This retry
keeps the source unchanged and accepts only the complete, source-pinned
warning log after path normalization. Five mutation checks reject added,
missing and altered warnings, an added error and an added `sorryAx`. This
exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 5.616
seconds; the exact warning verifier and final guards passed at 320/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`ec75f59276edce16ed1ef9180ca9e5cf67f10bcdedcf96431c72e4d81ab4f8ff`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `b04134d2874e123226706faa519154a0ec76055a5cb89f04eeead75be368e6bf`,
`e787a3b26247404a26393a23b7b5ea88ed1f261dcefa758c3a9bedc4278ddb0b`,
`c7095d0df40a8db77400b7ef35ef0346c856ac040aef77ebb4c651d04b3e36d3`,
`075ee173653396045b7b41f216e23433442f186125a51a6098e743cb4a26c7d1`, and
`0c383d4cd903e15e0df0ca62bb55d6227b79a4ac16bf594c0bed1c675978dfcc`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,491,428 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
105 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
