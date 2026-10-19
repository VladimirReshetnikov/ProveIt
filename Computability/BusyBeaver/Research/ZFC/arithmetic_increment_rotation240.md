# Internal marked-target increment for Rotation240

[`ArithmeticIncrementRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticIncrementRotation240.lean)
proves the complete increment excursion from a marked target in every IΣ₁
model. Finite prefix/suffix registers have arbitrary internal values, the
number of value-one spares is an arbitrary internal count, and the entire
left tape is arbitrary. The right exterior after the spares is explicitly
blank.

The operation restores every prefix/suffix value, increases the target by
one, and appends exactly one `011` spare. With `fileClock` summing encoded
register widths, the exact positive clock is
`2*fileClock pre + 2*value + 2*fileClock rest + 6*count + 11`.
The proof composes the checked carry traversal and six-step end pulse, then
returns across the spares, suffix, target and prefix. Its spare-return
induction quantifies both complete tape halves inside the model.

The [actual run](results/arithmetic-increment-rotation240-verification.json)
passes 11 axiom probes and 13 typed callers, with zero warnings and only
standard axioms. Source/audit times are 7.351/2.625 seconds under default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. The guard
uses 39 project prerequisites, four direct external boundaries, a retained
Seq boundary and Init/Omega, supplied by the actual EndPulse and Traversal
checks. No dependency rebuild or whole-cache attestation is claimed.

The [publication record](results/arithmetic-increment-rotation240-publication.json)
and [history](arithmetic-increment-rotation240/history.json.gz) preserve the
source, separate typed audit, raw logs, guard and independent source review.
Historical scratch paths remain in the records. This is a register-operation
endpoint; the represented dispatch/frame simulation and final PA equivalence
for the binary machine remain to be assembled. Attribution remains with
Mira-Cult, Jeff Ketchersid, Andrew James Wade and the maintained ProveIt work.
