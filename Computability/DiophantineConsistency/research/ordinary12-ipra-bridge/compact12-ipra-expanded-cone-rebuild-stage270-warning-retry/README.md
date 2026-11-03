# Expanded compact/iPRA rebuild: stage 270 exact-warning retry

The rejected attempt emitted one unused section-instance warning. The theorem
is used later in the same source, so this retry preserves the source and its
interface. It accepts only the complete, source-pinned warning log after path
normalization. Mutation checks reject added, missing and altered warnings, an
added error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and the rejected attempt's dependency guards. It
quarantined the rejected object and rebuilt the unchanged source. Lean exited
0 in 2.817 seconds; the exact warning verifier and final guards passed at
270/425, with source and direct dependencies unchanged. Retry and quarantined
object SHA-256s both equal
`f72e7e6f13676cc4675e402cd479124cfe70a222cabc1d041cf6b38be79242bb`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `f5a04f53a579d497ce3be3368f4ff377425a96edde3e33ab493ef800e3305966`,
`d810ac2f4b56d1383cf8a689dccc0b41187992625598078d7984ae52fa31140d`,
`c02c9690e3e5fc45eaaddc4d9377f48067984adc34188db64a4990cb80c354b7`,
`ca07d92b5a7ddb0f827e2f4f1d3296b04091405a16569cb60d6d90d2fc6ae39d`, and
`b65818a868c530d4826bb4ec55f9c51ef89f13f25f7805566678175f480d5d25`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,502,132 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
155 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
