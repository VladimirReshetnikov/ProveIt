# Internal marked-target decrement for Rotation240

[`ArithmeticDecrementRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticDecrementRotation240.lean)
proves both decrement branches in every IΣ₁ model, with arbitrary internal
register values and complete tape contexts. The finite crossed prefix is
restored, and neither branch appends a spare.

For a positive target `value+1`, the result contains `value` and exposes the
one added gap cell. Its exact clock is `2*fileClock pre + 4`. The zero branch
restores the target and needs a following ordinary register block, which may
be a value-one spare; its clock is `2*fileClock pre + 7`. The spare invariant
`167+extra` supplies this following block even at the last physical register.
Both clocks are proved positive. No blank exterior is required.

The [actual check](results/arithmetic-decrement-rotation240-verification.json)
passes 12 axiom probes and 14 typed callers, with zero warnings and only
standard axioms. Source/audit times are 3.705/2.676 seconds under default proof
limits, sharing 120 seconds with one thread and 4,096 MiB. The guard reuses
the actual EndPulse and Traversal providers: 39 project prerequisites, four
direct external boundaries, retained Seq and Init/Omega. It does not rebuild
or attest the whole dependency cache.

The [publication record](results/arithmetic-decrement-rotation240-publication.json)
and [history](arithmetic-decrement-rotation240/history.json.gz) preserve the
exact source, typed audit, raw logs, guard and independent source review.
These are register-operation endpoints. The represented dispatch simulation
and final internal PA equivalence for the binary machine remain open.
Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and the
maintained ProveIt work.
