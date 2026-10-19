# Arithmetic run graph for the exact 240-state machine

[`ArithmeticMachineRunRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineRunRotation240.lean)
defines a fixed Σ₁ run graph, and a Δ₁ definition of the same function, for
the literal source-rotation240 machine. Primitive recursion gives total unique
evaluation at every internal time in every IΣ₁ model. A separate induction
proves that its interpretation over the natural numbers agrees with the actual
machine run at every time, without a cutoff.

The initial configuration is code 1: the blank tape in canonical state 0.
Each successor applies the [checked 240-state transition
formula](arithmetic_machine_step_rotation240.md). The source defines a closed
parameter-free Σ₁ halting sentence and proves that its natural-number
interpretation is exactly blank-tape halting of `machineRotation240`. It also
proves a closed totality sentence in IΣ₁ and PA. This does not yet prove the
internal machine-to-validator comparison or the PA consistency equivalence.

The [arbitrary-initial evaluator](arithmetic_machine_run_from_rotation240.md)
now supplies internal run composition, full halted-configuration absorption
and recovery of this blank evaluator.
The [finite arithmetic startup](arithmetic_bootstrap_rotation240.md) proves
the exact 409,691-step boot equation in IΣ₁ and PA.

The [actual check](results/arithmetic-run-rotation240-verification.json) passes
14 named axiom probes and 16 typed callers, with zero warnings and only standard
Lean axioms. Source compilation took 12.505 seconds and the audit 2.153 seconds,
sharing a 120-second deadline with one thread, 4,096 MiB and default proof limits.
The first attempt timed out at 120 seconds with no diagnostic and no completed
object. Its input postchecks passed. The successful second attempt used exactly
the same source, audit, guard and limits. Low observed compiler CPU use and high
system I/O pressure motivated that retry; the timeout's cause is not established.
Both attempts remain in the [history](arithmetic-run-rotation240/history.json.gz).
The [completed-run review](arithmetic-run-rotation240/actual-run2-review.json)
checks the actual logs, inputs, providers and retained failure. It discloses that
the reviewer authored the original port and guard; it is an additional evidence
review, not an independent authorship claim.

The guard selects 26 project prerequisites, three explicit cached
Foundation/Mathlib boundaries and Init/Omega, using the actual 240-state step
record. It checks current source/object identities, the first providers Lean
will load, pinned dependency repositories and the fresh source object before
and after the typed audit. It reuses the dependency cache without rebuilding it
or attesting every file in that cache.

The [publication record](results/arithmetic-run-rotation240-publication.json),
[guard, audit and raw logs](arithmetic-run-rotation240/), and history preserve
the executed bytes and preparation. Historical scratch paths are retained;
publication does not supply cached objects or claim a clean-checkout rebuild.
Attribution follows Mira-Cult, Jeff Ketchersid, Andrew James Wade and the ProveIt
reductions. Generic arithmetic helpers retain their earlier Perm252 names;
the concrete table and new run definitions here are the 240-state ones.
