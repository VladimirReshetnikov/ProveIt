# Compact/iPRA exploratory rebuild: stages 11–15

This bounded author-side batch resumed the previous merged-root build. Before
compiling, the runner rechecked all 441 pinned sources, the complete selected
provider overlay, every previous stage output and log hash, and all previous
direct dependency and companion guards. Lean compiled stages 11–15 in pinned
source-import order; each exited 0 without warnings or `sorryAx`. Copied
sources, direct dependencies, guards, output hashes and logs are retained
under `observations/stage-11` through `stage-15`. The wrapper exited 0 after
its post-batch checks and reported `completed: 15, total: 59`.

The exact runner used is `run.py`, SHA-256
`5d00b46ad5a0c58835c64dc8af71308fe0f0c12c9192aa89febd7270ac164972`.
It reads the earlier receipts from the sibling `...-merged` and
`...-merged-next` directories. All three packets are needed to inspect this
prefix.

This is an exploratory author prefix, not an iPRA endpoint, paired replay or
complete ancestry audit. The 59-module static cone considers only the 441
source modules in the `DiophantineConsistency.*` namespace. Selected
conflicts also exist in other namespaces including `BusyBeaver.*`, so that
cone must not be considered complete without further reverse-impact analysis.
The remaining steps and model-to-iPRA join have not been checked. File and
resource guards are point-in-time.
