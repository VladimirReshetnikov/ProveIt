# Preliminary post-merge impact sizing

This source-only scan was taken after the `PRAWitnessPR` and
`PRAWitnessZFCAxioms` edits, before the subsequent `ZFCinPA.LStep*` merge. It
found exactly those two changed workspace source hashes and a 21-module reverse
closure in the captured source graph augmented with the recorded environments
of retained parent objects. The two edited files had unchanged explicit import
lists. The observed Git HEAD and input hashes are recorded in `manifest.json`;
the scan and source recheck exited zero.

This is a prospective size estimate, **not** an authenticated successor plan or
proof. In particular, it has not checked physical object origins, Lean's current
dependency parser, external companions, the still-running 258-module parent or
its comparison. It must be recomputed after subsequent merges. Its manifest
SHA-256 is `3ee106ad65ccec526627a1994e1c16df1ebbe090e79cd8d89b4a53378962dad6`.
