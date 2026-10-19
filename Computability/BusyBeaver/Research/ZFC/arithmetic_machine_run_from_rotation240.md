# Exact 240-state arithmetic runs from arbitrary configurations

[`ArithmeticMachineRunFromRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineRunFromRotation240.lean)
iterates the exact 240-state transition from every internal configuration code,
at every internal time in every IΣ₁ model. Its fixed Σ₁/Δ₁ graph is total and
unique. It agrees with the [blank-run evaluator](arithmetic_machine_run_rotation240.md)
when the initial code is 1, and with ordinary natural-number iteration on every
natural input.

The internal composition law is
`runFrom (t + u) initial = runFrom u (runFrom t initial)`.
Once the state code is zero, every later run preserves the entire encoded
configuration, including both tape halves. These facts permit a finite startup
prefix and later simulation segments to be composed without restricting their
internal clocks to standard natural numbers. Generic lookup lemmas also identify
every fixed natural transition key in every IOpen model.

The [actual check](results/arithmetic-run-from-rotation240-verification.json)
passes 19 named axiom probes and 23 typed callers, with zero warnings and only
standard Lean axioms. The first actual source/audit pair passed in 5.738 and
2.734 seconds. It used one thread, 4,096 MiB, default proof limits and one shared
120-second deadline. The checked blank-run result supplies the actual parent;
its earlier failed attempt is not accepted as a parent.
The [completed-run review](arithmetic-run-from-rotation240/review.json) checks
all 184 current inputs, the raw logs, exact import closure and fresh-object
captures. The reviewer discloses authorship of the earlier source port; this
additional evidence review does not claim independent source authorship.

The exact import closure contains 27 project prerequisites, three explicit
cached Foundation/Mathlib boundaries, and Init/Omega. The guard checks their
source/object identities and actual first providers, and records the new
source object before the typed audit. It does not rebuild dependencies or
attest the whole dependency cache.

The [publication record](results/arithmetic-run-from-rotation240-publication.json),
[guard, audit and raw logs](arithmetic-run-from-rotation240/), and
[history](arithmetic-run-from-rotation240/history.json.gz) preserve the source
plans, frozen actual parent and execution. The guard retains historical scratch
paths; publication does not provide cached objects or a clean-checkout rebuild.
The concrete startup, binary-to-register simulation and PA consistency
equivalence remain separate obligations. Attribution follows Mira-Cult,
Jeff Ketchersid, Andrew James Wade and the ProveIt reductions.
