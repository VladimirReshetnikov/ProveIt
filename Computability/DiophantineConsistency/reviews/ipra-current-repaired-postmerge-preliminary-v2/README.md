# Preliminary post-merge impact sizing

This source-only scan follows the five workspace source edits to
`PRAWitnessPR`, `PRAWitnessZFCAxioms`, `ZFCinPA.LStepAnd`, `LStepBasic` and
`LStepEx`. It found those five changed hashes and a 76-module reverse closure
in the captured source graph augmented with recorded retained-parent object
environments. The five edited files had unchanged explicit import lists. The
observed Git HEAD and input hashes are in `manifest.json`; the scan and source
recheck exited zero.

This is a prospective size estimate, **not** an authenticated successor plan or
proof. In particular, it has not checked physical object origins, Lean's current
dependency parser, new source snapshots, the still-running 258-module parent or
its comparison, or external companions. The 258 outputs and retained project
environments must be reauthenticated after the parent passes, and any later
source changes must be incorporated. The earlier two-edit scan is preserved in
the adjacent `ipra-current-repaired-postmerge-preliminary` packet.

Manifest SHA-256: `4482a88e788ad7d6e3ec960ebcfe279f05c3b55d2f441e50b7cda2a2e591859c`.
