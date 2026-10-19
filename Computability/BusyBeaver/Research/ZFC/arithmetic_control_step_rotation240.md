# Exact Rotation240 control-step equations

[`ArithmeticControlStepRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticControlStepRotation240.lean)
connects each checked catalogue entry to the represented register interpreter's
step. It proves the opcode lookup, the complete packed-row equation, increment,
both decrement branches, break, continue and halt. Every nonhalting successor
resolves to a valid catalogue control with a nonzero opcode.

The 6,455 controls are external finite syntax; the register file ranges over
arbitrary IΣ₁-model elements. The proofs reuse the actual table-row identity
and the catalogue-independent `ArithmeticControlTable.spec_get` theorem.
They do not compute the large concrete table again. Physical selectors and
successor numbers come from the exact Rotation240 source catalogue.

The [actual check](results/arithmetic-control-step-rotation240-verification.json)
passes ten axiom probes and ten typed callers with zero warnings and only
standard axioms. Source and audit took 3.074 and 2.389 seconds under default
proof limits, within a shared 120-second limit using one thread and 4,096 MiB.
The sole checked Catalogue parent supplies 659 project prerequisites; no
dependency family is rebuilt. The [publication record](results/arithmetic-control-step-rotation240-publication.json)
and [history](arithmetic-control-step-rotation240/history.json.gz) retain the
source, audit, logs, direct guard and independent source review.

These equations identify the logical side of each simulated instruction.
Binary runtime composition and the complete halting equivalence are separate
obligations. Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James
Wade and the existing ProveIt interpreter framework.
