# Removing the exact 240-state startup in PA

[`ArithmeticStartupRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticStartupRotation240.lean)
proves in IΣ₁ and PA that the fixed blank-halting sentence is equivalent to
the fixed sentence for halting from the complete boot configuration. This
removes the checked 409,691-step startup from the internal arithmetic problem.

The general shift theorem works for arbitrary internal offsets, times and
initial configuration codes in every IΣ₁ model. Two iteration blocks commute;
if the machine has already halted, its whole configuration is absorbing.
Consequently the equivalence also covers a prefix extending beyond a halt,
without assuming that the boot state is live. The
[finite boot equation](arithmetic_bootstrap_rotation240.md) specializes this
theorem to the literal seed code. Both halting sentences have fixed Σ₁ syntax,
and the seed sentence's interpretation over the natural numbers agrees with
halting of the exact binary table.

The [actual check](results/arithmetic-startup-rotation240-verification.json)
passes 12 named axiom probes and 14 typed callers, with zero warnings and only
`propext`, `Classical.choice` and `Quot.sound`. Source compilation took 3.047
seconds and the audit 2.081 seconds on the first attempt. They shared a
120-second deadline with one thread, 4,096 MiB and default proof limits.

The two actual parents are the
[arbitrary-initial run](arithmetic_machine_run_from_rotation240.md) and the
[finite bootstrap](arithmetic_bootstrap_rotation240.md). Their selected union
contains 43 project prerequisites, four explicit cached Foundation/Mathlib
boundaries and Init/Omega. The guard checks the 312 input identities, first
providers and fresh source object before and after the audit. Parent evidence
retains its inherited generic 252-state and legacy provenance; dependencies
were reused without a rebuild or a claim to attest the whole cache.

The [source review](arithmetic-startup-rotation240/source-review.json) and
[completed-run review](arithmetic-startup-rotation240/review.json) independently
check the mathematical scope and actual evidence. Their readers and notes are
preserved in the [review history](arithmetic-startup-rotation240/review-history.json.gz).
The [publication record](results/arithmetic-startup-rotation240-publication.json),
[guard, audit and raw logs](arithmetic-startup-rotation240/), and
[execution history](arithmetic-startup-rotation240/history.json.gz) preserve the
executed bytes and preparation. Historical scratch paths remain in these
records; publication does not supply cached objects or a clean-checkout build.

The unbounded internal binary-to-register simulation and the final PA
consistency equivalence remain open. This theorem closes startup removal,
not those bridges. Attribution follows Mira-Cult, Jeff Ketchersid, Andrew James
Wade and the ProveIt reductions.
