# Expanded compact/iPRA rebuild: stage 306 exact-warning retry

The rejected attempt emitted one unused `hw` binder warning; the lemma is
called positionally in the same source. This retry keeps the source unchanged
and accepts only the complete, source-pinned warning log after path
normalization. Five mutation checks reject added, missing and altered warnings,
an added error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and the rejected direct dependency guards. It
quarantined the rejected object and rebuilt the unchanged source. Lean exited
0 in 17.513 seconds; the exact warning verifier and final guards passed at
306/425, with source and direct dependencies unchanged. The retry and
quarantined object SHA-256s both equal
`021f78a695755002890c3f881601fc9197e50147cdc73776738f675d7fafc964`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `786196f7968c41550a12ca2c1a80ce1cc7e096e70aa94f016b94d1d1e860b237`,
`fc480fef80f60323fd1b50a4d61c2b004d1e590c25b8455527d0b86a84a300a6`,
`058a4167adde870fdbacb865da687417046ac070c86a7bc7304bf550aecc9ac7`,
`63dd2d1f061ac69f0a00b9b31d6f063b3cf4ec33e03aa6a33bb7e02ee857a593`, and
`918245a5afe6d684ba7c476fc776d7e91ebe74ccfe8cde0114bf355272da63d2`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,403,292 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
119 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
