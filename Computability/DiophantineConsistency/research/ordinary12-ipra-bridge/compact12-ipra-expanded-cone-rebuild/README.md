# Expanded compact/iPRA endpoint rebuild: first author batch

The fresh merged-root author build uses the full selected-project
serialized-import analysis and its conservative 425-module endpoint
candidate cone. It removes the 366 affected nine-selected objects from the
old 2,557-file overlay, keeps the other selected objects as guarded symlinks,
and writes rebuilt modules as regular files in the same fresh library root.
The other 59 candidate families were already absent from the old overlay.
The runner follows the pinned candidate topological order, verifies the 425
current source hashes and full original/merged overlay, guards each direct
dependency and companion, and stops on a missing input, warning, error or
resource bound. It never overwrites the earlier 15-stage exploratory build.

The first batch compiled these five sources from the current canonical
`Computability/BusyBeaver/Lean` tree:

1. `BusyBeaver.ZFC.ArithmeticControlBisim`
2. `BusyBeaver.ZFC.ArithmeticControlFile`
3. `BusyBeaver.ZFC.ArithmeticHistoryRecurrence254`
4. `BusyBeaver.ZFC.ArithmeticPositiveSimulation254`
5. `BusyBeaver.ZFC.ArithmeticProofConstructors254`

All five bounded Lean processes exited 0 with no warnings or `sorryAx`.
The wrapper then rechecked the pinned source/overlay, all built outputs and
direct dependency/companion guards, and exited 0, reporting `5/425`. Source
copies, direct dependency lists, raw logs, commands, hashes, guards and
receipts are retained in `observations/batch-001/`. The generated complete
baseline lists all retained symlinks, 425 removed families, source pins and
the topological order under `observations/baseline.json`.

The exact runner is `run.py`, SHA-256
`c268533ca55c6eeba33066d591f0b5eff5bd6dd52e107350d924420bfe2350e6`;
`observations/baseline.json` has SHA-256
`f89d5466637be18ca5e95492df05e329a8ccc1be6d9fb150602fc975089b1aea`.
The run's point-in-time direct guards do not authenticate inherited package,
transitive or dynamic ancestry. Current source imports match the selected
object graph, but current source is not thereby authenticated as the origin
of the historical selected objects. This five-module author prefix is not
an iPRA endpoint, full coherent build or paired replay; the remaining 420
modules and the compact model-to-iPRA client remain unproved by this run.
