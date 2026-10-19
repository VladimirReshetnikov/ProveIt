# Arithmetic transition lookup for the exact 240-state machine

[`ArithmeticMachineGraphRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineGraphRotation240.lean)
defines a fixed bounded arithmetic formula for the published machine's
transition lookup. It is total in every IOpen model. A kernel-checked finite
theorem identifies all 480 actions with `machineRotation240.transition`.
The numeric rows are derived directly from the imported canonical table.

Source-state keys are canonical state plus one. A missing source key returns
zero; read bit zero selects the first action and a nonzero bit selects the
second. Actual tape bits are zero or one. Action codes are positive, so the
terminal write-one/right action is code 4 and retains its write and movement.
The initial read-zero action is code 392. The generic upper bound 1,012 is
preserved for reuse by the arithmetic step construction.

The [actual check](results/arithmetic-graph-rotation240-verification.json)
passed eight named theorem probes and eight typed callers with zero warnings.
Source and audit took 63.531 and 1.592 seconds. They shared a 120-second
deadline with one thread, 4,096 MiB and default proof limits. The audit reports
only `propext`, `Classical.choice` and `Quot.sound`.

The guard selected 23 project modules, three explicit cached Foundation/Mathlib
boundaries, and Init/Omega from successful parent records. It checked the
selected source/object identities, first import providers and pinned dependency
repositories before and after execution. It did not rebuild dependencies or
attest the entire transitive dependency cache.

The [publication record](results/arithmetic-graph-rotation240-publication.json),
[original guard, audit and raw logs](arithmetic-graph-rotation240/), and
[lossless text history](arithmetic-graph-rotation240/history.json.gz) retain the
successful bytes and preparation. The original guard uses historical scratch
and provider paths. Publication performed no proof replay.

This begins the arithmetic specialization to the active 240-state table.
The older [246-state step and run development](arithmetic_machine_step_prefix246.md)
still needs its corresponding 240-state specialization. The all-internal
register/binary simulation and final PA consistency equivalence remain open.
The original machine and compiler retain Mira-Cult, Jeff Ketchersid, Andrew
James Wade and the subsequent ProveIt reductions' attribution.
