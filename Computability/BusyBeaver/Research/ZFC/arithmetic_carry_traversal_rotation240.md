# Internal carry traversal for Rotation240

[`ArithmeticCarryTraversalRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticCarryTraversalRotation240.lean)
proves carry and rollback across any internal number of value-one spare
registers, followed by composition with a finite physical register file.
Every register value and both complete numeric tape halves are arbitrary
elements of an IΣ₁ model. The nine-slot clients use a finite `Fin 9` file;
the unbounded spare count is an internal arithmetic value.

The carried spare code repeats `101`, with recurrence `8*x+5`; the original
spare code repeats `011`, with recurrence `8*x+6`. Both functions have total
internal representations. Π₁ induction quantifies both changing tape halves
and proves the exact `3*count` traversal clocks. Rollback restores the entire
original encoding, including arbitrary tape beyond the spares. The zero-count
case is included.

The [actual run](results/arithmetic-carry-traversal-rotation240-verification.json)
passes 15 axiom probes and 17 typed callers, with zero warnings and only
standard axioms. Source/audit times are 10.351/2.676 seconds under default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. The check
reuses 37 project prerequisites, four direct external boundaries, a retained
Seq boundary and Init/Omega from the actual Carry and OneBlocks checks.
Existing caches were not rebuilt or wholly attested.

The [publication record](results/arithmetic-carry-traversal-rotation240-publication.json)
and [history](arithmetic-carry-traversal-rotation240/history.json.gz) preserve
the exact source, typed audit, raw logs, guard and independent source review.
Historical scratch paths remain in the execution records. These endpoint
equalities are ingredients for register operations; they do not yet provide
the complete represented dispatch simulation or PA machine endpoint.
Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and the
maintained ProveIt construction.
