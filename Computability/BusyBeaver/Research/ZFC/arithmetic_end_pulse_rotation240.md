# Internal end pulse for Rotation240

[`ArithmeticEndPulseRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticEndPulseRotation240.lean)
proves marker restoration, both pulse branches, the carry scan, and the
six-step end window of the exact 240-state machine in every IΣ₁ model.
The window needs four leading zero cells and preserves arbitrary tape beyond
them: a right code `16*suffix` becomes `8*suffix+6`. Its blank specialization
supplies the new `011` spare block and enters the return state. The complete
left tape is retained in the explicit endpoint equation.

The [actual run](results/arithmetic-end-pulse-rotation240-verification.json)
passes eight axiom probes and eight typed callers, with zero warnings and
only standard axioms. Source/audit times are 4.309/2.073 seconds under default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. Ten literal
transition facts are checked in the source. The guard reuses 36 project
prerequisites, four direct external boundaries, a retained Seq boundary and
Init/Omega from the actual Carry check; caches were not rebuilt or wholly
attested.

The [publication record](results/arithmetic-end-pulse-rotation240-publication.json)
and [history](arithmetic-end-pulse-rotation240/history.json.gz) preserve the
source, separate typed audit, raw logs, guard and independent source review.
Execution records retain historical scratch paths. This unit supplies local
endpoints for the increment composition, not a first-exit theorem or the
complete binary/interpreter simulation. Attribution remains with Mira-Cult,
Jeff Ketchersid, Andrew James Wade and the maintained ProveIt construction.
