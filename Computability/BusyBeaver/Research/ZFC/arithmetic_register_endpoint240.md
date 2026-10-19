# Checked internal register endpoint for Rotation240

In every model of IΣ₁, the represented validator accepts a proof of falsity
if and only if the Rotation240 control interpreter halts from the exact
logical seed. The unchanged
[`ArithmeticL2Endpoint254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2Endpoint254.lean)
now has a successful [local Lean check](results/arithmetic-l2-endpoint254-verification.json).

The proof checks the original program root's literal occurrence in its packed
catalogue, then transports scheduler execution through the register program.
Every nonhalting root invocation changes the candidate pointer or counter,
which makes its internal clock positive. The positive-clock simulation gives
both halting directions, including for nonstandard internal execution times.
The already checked control certificate transfers that equivalence to the
Rotation240 interpreter.

The logical seed record is `[3,0,0,0,3,0,0,0,0]` in the `AS` field order;
its encoded physical register order is `[0,0,0,3,0,0,3,0,0]`. Both the seed
and packed table match the separate
[blank-machine/control connection](arithmetic_blank_control_rotation240.md).
The final composition draft retains the explicit adapters. This module's
conclusion is the register/control equivalence; the full PA equivalence with
Con(ZFC) still needs the validator calibration and final composition checks.

The check passes six named axiom probes and eight typed callers, with zero
warnings and only standard Lean axioms. Source and audit took 18.784 and
1.899 seconds under one thread, 4,096 MiB and a shared 120-second deadline.
The existing source limits of 100,000 recursion depth and 4,000,000 heartbeats
are retained; the audit uses defaults. Its exact boundary consists of 113
project source/object pairs, three external boundaries and Init/Omega, taken
from the actual scheduler and assembled-control-certificate results. The
[publication](results/arithmetic-l2-endpoint254-publication.json) preserves
the checks, source bindings, logs and review history, including the scheduler's
five inherited source warnings.
