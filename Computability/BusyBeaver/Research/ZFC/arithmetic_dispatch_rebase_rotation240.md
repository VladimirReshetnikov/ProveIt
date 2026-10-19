# Returning to the canonical Rotation240 dispatch frame

[`ArithmeticDispatchRebaseRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticDispatchRebaseRotation240.lean)
identifies the complete outgoing tape with the canonical frame of its next
accepted control. The actual checked catalogue resolves the consumed path,
including implicit zero bits, and the existing clean-path theorem supplies
the remaining zero padding. Numeric files, gaps, spare counts and clocks are
arbitrary IΣ₁-model elements.

The frame uses state code 85 and a 64-bit pointer margin. The finite added
padding `padExtra` is separate from the internal spare count `spareExtra`:
positive decrement has `padExtra=1` and preserves the spare count; increment
adds a spare. The final target theorem uses the actual packed-table successor
number. No tape exterior is discarded in these identities.

The [actual check](results/arithmetic-dispatch-rebase-rotation240-verification.json)
passes 16 axiom probes and 18 typed callers with zero warnings and only
standard axioms. Source and audit took 3.541 and 2.730 seconds under default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. Existing
FiniteTape, FrameData and RuntimeInstance providers were reused; complete
catalogue coverage was not recomputed. The
[publication record](results/arithmetic-dispatch-rebase-rotation240-publication.json)
and [history](arithmetic-dispatch-rebase-rotation240/history.json.gz) retain
the exact inputs, logs, guard and independent source review.

The dynamic reentry theorem still takes the numeric instruction endpoint and
its positive clock as premises. This unit proves the necessary tape and
control identification, not those runtime premises or the full PA endpoint.
Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and
the maintained ProveIt work.
