# Internal register-program prerequisites

Three unchanged upstream modules now have fresh local Lean checks for the
register side of the 240-state PA comparison.

[`ArithmeticDagRun`](../../Lean/BusyBeaver/ZFC/ArithmeticDagRun.lean) proves
structured execution from an occurrence in a finite decoder tree, including
increment and iteration for arbitrary internal register values and times.
The iteration proof fixes the external finite occurrence before applying
Σ₁ induction to the internal iteration count. Its row, step and run
hypotheses remain explicit. The [actual check](results/arithmetic-dag-run-verification.json)
passes three probes and three typed callers with zero warnings. Source and
audit took 10.250 and 1.696 seconds. The source retains its existing recursion
limit 8,192 and heartbeat limit 4,000,000; the audit uses defaults.

[`DagControl254`](../../Lean/BusyBeaver/ZFC/DagControl254.lean) specializes
the row-lookup specification to the exact packed original register-program
table. Its [actual check](results/dag-control254-verification.json) passes
one probe and one typed caller with zero warnings, in 1.625 and 1.505 seconds,
using default source and audit proof limits. This generic lookup result
does not itself evaluate the complete concrete bisimulation certificate.

[`ArithmeticL2Lib254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2Lib254.lean)
then specializes structured execution to the program's nine-register layout.
It proves transfer, copying, clearing, pairing and unpairing with all other
register fields preserved, for arbitrary internal counters. The
[actual check](results/arithmetic-l2-lib254-verification.json) passes four
probes and four typed callers with zero warnings, in 24.285 and 1.667 seconds.
The unchanged source retains its 8,192 recursion and 4,000,000 heartbeat
limits; the audit uses defaults. Forty project prerequisites are selected
from the first two checks and the exact historical `Dag254` provider.
The [publication](results/arithmetic-l2-lib254-publication.json) preserves
the selected historical binding without claiming a new check of its entire
ancestor input collection.

All three runs use one thread, 4,096 MiB and a shared 120-second source-and-audit
deadline. The first two guards select 35 and 37 exact project prerequisites,
respectively, from already checked parents, with three external source/object
boundaries and Init/Omega. Inputs, first providers and fresh objects are
checked before and after the audit; all reported axioms are standard Lean
axioms. None of these runs rebuilds dependencies or claims to attest the entire
dependency cache.

The [DagRun publication](results/arithmetic-dag-run-publication.json) and
[DagControl publication](results/dag-control254-publication.json) preserve
the source bindings, audits, guards, logs and author history. These are
prerequisites of the remaining register macros and scheduler checks. The
[final PA composition](rotation240_pa/final-composition-plan/README.md)
still requires the remaining register and validator dependencies and its
own successful compilation.
