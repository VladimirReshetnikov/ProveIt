# Arithmetic one-step graph for the exact 240-state machine

[`ArithmeticMachineStepRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineStepRotation240.lean)
defines a fixed bounded arithmetic formula for one machine step. It is total
and unique on every input in every IOpen model. On every natural configuration
code it equals the exact table's numeric transition, with no bound on the tape
or configuration code.

The proof reuses generic Cantor coding and tape arithmetic, specializing the
[checked lookup](arithmetic_machine_graph_rotation240.md). Halted codes and
invalid positive state codes preserve both tape halves. The terminal action
at canonical state 68 (state code 69) writes one, moves right, and sets the
state code to zero; the audit checks that complete effect.

The [actual check](results/arithmetic-step-rotation240-verification.json)
passed seven named probes and ten typed callers, with zero warnings. Source
and audit took 39.300 and 1.819 seconds, sharing a 120-second deadline with
one thread, 4,096 MiB and default proof limits. All reports use only standard
Lean axioms.

The guard selects 25 project modules, three explicit cached Foundation/Mathlib
boundaries and Init/Omega from the checked 246-state step and 240-state lookup.
It verifies the selected source/object identities, first providers and pinned
dependency repositories. It does not attest the entire dependency cache.
The [publication record](results/arithmetic-step-rotation240-publication.json),
[guard, audit and raw logs](arithmetic-step-rotation240/), and
[lossless history](arithmetic-step-rotation240/history.json.gz) preserve the
successful bytes and preparation. The guard retains historical scratch paths.

[Iteration is now checked](arithmetic_machine_run_rotation240.md), including
totality in IΣ₁/PA and agreement with every ordinary-natural machine run.
The [finite arithmetic startup](arithmetic_bootstrap_rotation240.md) is also
checked. The unbounded internal machine-to-validator comparison remains open. Attribution
follows Mira-Cult, Jeff Ketchersid, Andrew James Wade and the ProveIt reductions.
