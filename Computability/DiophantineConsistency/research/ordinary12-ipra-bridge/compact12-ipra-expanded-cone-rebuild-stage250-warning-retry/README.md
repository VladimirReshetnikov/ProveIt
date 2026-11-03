# Expanded compact/iPRA rebuild: stage 250 exact-warning retry

The stopped attempt emitted three `unnecessarySimpa` style warnings. This
retry preserves the source, theorem statements and existing source pins. It
accepts only the complete, source-pinned three-warning text after normalizing
the source paths. Mutation checks reject added, missing and altered warnings;
the baseline includes no `error:` or `sorryAx`. This is a warning exception,
not an independent proof audit.

The runner checked the 425 source pins, selected overlay, prior receipts and
warning baselines, and the rejected attempt's direct dependency guards. It
quarantined the exact rejected object, recompiled the source, and checked the
baseline again. Lean exited 0 in 2.466 seconds; source and direct guards were
unchanged, and the wrapper passed its final guards at 250/425. The retry and
quarantined objects both have SHA-256
`417c68884d4f44ded4c2a8beccc05f85ee10739a49057c2bf6427acc82d918d5`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `e46032e3cee19b2ba97f6d8bf76547aa422cceee41759ddcd282dc419e90cc9d`,
`0438b6c8cd26dbd24c5b9409df156fedf879cf9f92f5bad7d378640a3827ef58`,
`4907ef8efcf1fb484476b1ea67f1bdf595432f1b3df358ca7ee4a336395794f1`,
`45c04e3ace2b77f1f06d51ee3058f5148f1692b31df2f4a12c3eda787637352d`, and
`50db07e39ae5824530d9d745acff433947bc4e01203b0f234266ff519ecb6ee2`.
Raw observations, verifier tests and quarantine receipt are retained.

Five-second monitoring saw no Lean child and minimum sampled MemAvailable
18,659,024 KiB; short children and overlaps can be missed between samples.
This author prefix is not an iPRA endpoint, independent replay, or complete
provider audit. 175 stages and the compact model-to-iPRA join remain; package
and dynamic ancestry are not authenticated.
