# Represented whole-frame data for Rotation240

[`ArithmeticControlFrameDataRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticControlFrameDataRotation240.lean)
defines the arithmetic relation between a coded register state and its whole
binary dispatch frame. It uses the exact 6,455-control catalogue, state code
85, a 64-bit pointer margin, nine physical register fields, and
`oneBlocks (167+extra) 0` for the spare tail. Register values, gap and extra
spares are arbitrary elements of an IΣ₁ model.

The file, pointer and frame functions have explicit arithmetic definitions.
The resulting `Related` relation is Σ₁-definable, excludes halted or invalid
logical controls, and implies that the binary frame is active. A nonzero
opcode selects an actual catalogue control. The spare tail always supplies
the following ordinary block required by a zero decrement at the last field.

The [accepted check](results/arithmetic-control-frame-data-rotation240-verification.json)
passes 18 axiom probes and 18 typed callers with zero warnings and only
standard axioms. Source/audit times are 7.609/2.514 seconds under default proof
limits, sharing 120 seconds with one thread and 4,096 MiB. The actual Catalogue
and Traversal providers supply 674 project prerequisites, four direct external
providers, retained Seq and Init/Omega; no dependency family is rebuilt.

The [history](arithmetic-control-frame-data-rotation240/history.json.gz)
preserves the initial elaboration failure and accepted repair. A generic
variable-table support lemma avoids unfolding the large concrete table during
elaboration, and identical conditional branches simplify with `ite_self`.
No public statement or proof limit was weakened. The
[publication record](results/arithmetic-control-frame-data-rotation240-publication.json)
preserves exact sources, audit, logs, guard and independent source review.

This relation supplies data and definability for the existing positive-clock
simulation theorem. Its step, halting and initial-frame premises still need
to be connected; this unit does not establish the binary PA endpoint.
Machine and framework attribution remains with Mira-Cult, Jeff Ketchersid,
Andrew James Wade and the maintained ProveIt work.
