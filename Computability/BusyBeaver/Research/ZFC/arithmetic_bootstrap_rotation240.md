# PA proof of the exact 240-state startup

[`ArithmeticBootstrapRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticBootstrapRotation240.lean)
proves that the fixed arithmetic run reaches the complete encoded boot
configuration after exactly 409,691 steps, in every IΣ₁ model. IΣ₁ and PA prove
the corresponding closed arithmetic sentence. The configuration includes the
state and both numeric tape halves.

The proof first connects the [already checked literal startup](rotation240_runtime.md)
to the [exact arithmetic run](arithmetic_machine_run_rotation240.md) over the
natural numbers. Σ₁ function absoluteness then transports this fixed finite
result into every arithmetic model. The generic `run_cast` lemma applies to
each external natural time; it does not assert that every internal time is
standard. No new simulation of the 409,691-step prefix is performed here.

The [actual check](results/arithmetic-bootstrap-rotation240-verification.json)
passes seven named axiom probes and nine typed callers, with zero warnings and
only standard Lean axioms. Source compilation took 2.146 seconds and the audit
2.010 seconds on the first attempt. They shared a 120-second deadline with one
thread, 4,096 MiB and default proof limits.

Three actual parent records supply the prerequisites: the 240-state arithmetic
run, its checked final boot chunk, and the earlier 246-state arithmetic
bootstrap check. The last supplies the machine-parametric
`ArithmeticBootstrapPerm252.numericRun_of_zipRep` lemma and its dependencies;
the concrete 246-state bootstrap is not in the selected import closure.
The guard checks 41 project prerequisites, four explicit cached
Foundation/Mathlib boundaries, Init/Omega, the first providers and the fresh
source object before and after the audit. Legacy parent records retain their
original schema. The dependency cache is reused without a rebuild or a claim
to attest all of its contents.

The [publication record](results/arithmetic-bootstrap-rotation240-publication.json),
[guard, audit and raw logs](arithmetic-bootstrap-rotation240/), and
[history](arithmetic-bootstrap-rotation240/history.json.gz) preserve the
executed bytes, exact parent bindings and preparation. The guard retains
historical scratch paths; cached objects and a clean-checkout rebuild are not
supplied by publication.

This closes the finite arithmetic startup equation. The unbounded internal
binary-to-register simulation and the PA consistency equivalence remain open.
Attribution follows Mira-Cult, Jeff Ketchersid, Andrew James Wade and the ProveIt
reductions.
