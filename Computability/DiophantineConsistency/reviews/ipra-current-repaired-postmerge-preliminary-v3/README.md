# Preliminary post-merge impact sizing

This source-only scan follows six workspace edits: `PRAWitnessFormulaRec`,
`PRAWitnessPR`, `PRAWitnessZFCAxioms`, `ZFCinPA.LStepAnd`, `LStepBasic` and
`LStepEx`. It found exactly those six changed hashes and a 107-module reverse
closure in the captured source graph augmented with recorded retained-parent
object environments. The six edited files had unchanged explicit import lists.
The observed Git HEAD and input hashes are in `manifest.json`; the scan and
source recheck exited zero.

This is a prospective size estimate, **not** an authenticated successor plan or
proof. It has not checked physical object origins, Lean's current dependency
parser, new source snapshots, the still-running 258-module parent or its
comparison, or external companions. The 258 outputs and retained project
environments must be reauthenticated after the parent passes, and any later
source changes must be incorporated. The earlier two-edit and five-edit scans
are preserved in the adjacent preliminary packets.

Manifest SHA-256: `7815614e29f5a3cd05982bd1bd360ffc32190cc974e01344f1e2ee596d86e596`.
