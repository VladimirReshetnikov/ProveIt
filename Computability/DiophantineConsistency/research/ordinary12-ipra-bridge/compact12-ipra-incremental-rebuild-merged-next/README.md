# Compact/iPRA exploratory rebuild: stages 6–10

The bounded author-side second batch resumed the earlier merged-root build.
Before compiling it rechecked all 441 pinned sources, the complete selected
provider overlay, all first-five output/log hashes, and every earlier direct
dependency and companion guard. It then compiled stages 6–10 in the pinned
source dependency order; each Lean process exited 0 without warnings or
`sorryAx`. The copied sources, direct dependencies, guards, output hashes and
logs are retained in `observations/stage-06` through `stage-10`. Afterward
all full-overlay, source and prior-stage checks passed again. The batch
wrapper actually exited 0 and reported `completed: 10, total: 59`.

The exact runner used is `run.py`, SHA-256
`b722817de0b481e92a3b4a26a15191ba80db43389265f589d6399a7a582811a1`.
It reads the prior five receipts and snapshots from the sibling
`compact12-ipra-incremental-rebuild-merged` directory, and writes only to
its own evidence directory and the shared fresh merged build root.

This is an exploratory author prefix, not an iPRA endpoint, paired replay or
full dependency ancestry audit. The static cone remains restricted to the
441 source modules in the `DiophantineConsistency.*` namespace; other
namespace, package and dynamic import ancestry remains unverified. The
remaining 49 stages and eventual model-to-iPRA bridge have not been checked
by this batch. File and resource guards are point-in-time.
