# Internal selected-register marking for Rotation240

[`ArithmeticRegisterMarkRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterMarkRotation240.lean)
proves marking at each of the nine physical selectors in every IΣ₁ model.
The target's `01` header becomes `00`; all other cells in both complete tape
halves are preserved. Register values and the spare count are arbitrary
internal values. The exact positive clock is `2*fileClock pre + 3`; the return
state is code 2 for an empty prefix and code 4 otherwise.

The [accepted check](results/arithmetic-register-mark-rotation240-verification.json)
passes 15 axiom probes and 17 typed callers with zero warnings and only
standard axioms. Source/audit times are 4.382/2.767 seconds under default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. It binds the
actual internal Increment and external RegisterMark providers, with 44
project prerequisites, four direct external providers, retained Seq and
Init/Omega. The used transition rows are checked against the exact table.

The first attempt compiled the endpoints but reported two unused-instance
warnings and an audit failure at an open `decide` expression. The second
attempt misplaced `omit` after a documentation comment. The accepted third
attempt removes the unused instances and reduces the audit bound to a closed
natural-number proposition. The [history](arithmetic-register-mark-rotation240/history.json.gz)
preserves all three attempts, their exact sources, logs, guards and source
review; the [publication record](results/arithmetic-register-mark-rotation240-publication.json)
identifies the accepted bytes.

This is a whole-tape marking endpoint. First-exit properties, complete dispatch
and the internal binary simulation are not asserted here. Attribution remains
with Mira-Cult, Jeff Ketchersid, Andrew James Wade and the maintained ProveIt work.
