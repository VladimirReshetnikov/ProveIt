# Internal register-box interpretation for Rotation240

[`ArithmeticSymbolicBoxesRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicBoxesRotation240.lean)
interprets the actual symbolic box datatype as nine physical register fields
followed by `167+extra` one-valued spares. Register values, the extra count
and the following tape suffix range over arbitrary IΣ₁-model elements.
The identities split at any physical register, mark its header, and describe
increment and both decrement branches while preserving the other fields.

The permanent spare tail supplies a following complete block even at the
last physical register. Increment increases the extra count by one; decrement
preserves it. Positive decrement's additional cell belongs to the left tape
in the execution contract, not to this register prefix. Every interpreted
box starts with a zero bit, as required by the symbolic backward step.

The [actual check](results/arithmetic-symbolic-boxes-rotation240-verification.json)
passes 16 axiom probes and 18 typed callers with zero warnings and only
standard axioms. Source and audit took 3.726 and 2.538 seconds at default
proof limits, sharing 120 seconds with one thread and 4,096 MiB.
The [history](arithmetic-symbolic-boxes-rotation240/history.json.gz) preserves
the failed first run and all drafts. Its repair uses explicit congruence on
the block count to avoid unfolding the constant 167 during elaboration;
no statement or proof limit changed.

These are pure prefix identities. Actual box execution is supplied separately
by the checked Mark, Increment and Decrement contracts. The
[publication record](results/arithmetic-symbolic-boxes-rotation240-publication.json)
retains their selected prerequisites and the original source provenance.
Machine and framework attribution remains with Mira-Cult, Jeff Ketchersid,
Andrew James Wade and ProveIt.
