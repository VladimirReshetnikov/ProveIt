# Internal register-program prerequisites

Eight unchanged upstream modules now have fresh local Lean checks for the
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

[`ArithmeticL2Macros254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2Macros254.lean)
adds the stack and formula-constructor macros. Its
[actual check](results/arithmetic-l2-macros254-verification.json) passes four
probes and four typed callers with zero warnings, in 6.107 and 1.686 seconds.
The source retains its 8,192 recursion and 4,000,000 heartbeat limits;
the audit uses defaults and the guard reuses 41 project prerequisites.
The full output records distinguish completed macros that restore clean
scratch registers from the intermediate `pop110` and `read108` helpers,
which intentionally leave their output in `s1`. The
[publication](results/arithmetic-l2-macros254-publication.json) retains the
unchanged source and these exact contracts.

[`ArithmeticL2Control254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2Control254.lean)
proves destructive equality testing, fetch and the MP/NIP branches with
their exact normal, break and halt exits. Both tested registers are cleared
on either equality-test branch; the NIP halt case requires the explicit
falsity-code premise. Its [actual check](results/arithmetic-l2-control254-verification.json)
passes six probes and six typed callers with zero warnings, in 4.748 and
1.810 seconds. The source retains its 8,192 recursion and 400,000 heartbeat
limits; the audit uses defaults and 42 project prerequisites are reused.
The [publication](results/arithmetic-l2-control254-publication.json) keeps
the full-state contracts and all clean/cache premises explicit.

[`ArithmeticL2Axioms254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2Axioms254.lean)
composes the axiom subtree's exact register effects. Its final gate clears
the bundle on either prohibited equality and clears all three parameters;
the complete node-1 routine preserves clean scratch registers. The
[actual check](results/arithmetic-l2-axioms254-verification.json) passes three
probes and three typed callers with zero warnings, in 25.417 and 1.603 seconds.
The source retains its 8,192 recursion and 4,000,000 heartbeat limits;
the audit uses defaults and 43 project prerequisites are reused. This
composition result still needs the separate formula-evaluation theorem to
identify the constructed bundle with the validator's axiom operation.
The [publication](results/arithmetic-l2-axioms254-publication.json) preserves
the full source and the review of its literal decoder-tree compositions.

[`ArithmeticL2AxiomsEval254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2AxiomsEval254.lean)
gives the full closed forms of all nine register fields, including the final
gate, formula bundle and stack. These equalities hold for arbitrary internal
records without a clean-scratch premise. The
[actual check](results/arithmetic-l2-axioms-eval254-verification.json) passes
two probes and three typed callers with zero warnings, in 17.013 and 1.644
seconds, reusing 44 project prerequisites. The source retains its 8,192
recursion and 4,000,000 heartbeat limits and its existing disabled
unused-simp-argument linter; the audit uses defaults. An initial audit failed
because expected-type inference constrained a whole record before projecting
its field. Two local intermediate equalities fix the audit without changing
its statements or the proof source. Both attempts are retained in the
[publication history](arithmetic-l2-axioms-eval254/history.json.gz).
Identification with the named validator axiom operation is provided by the
following module.

[`ArithmeticL2Root254`](../../Lean/BusyBeaver/ZFC/ArithmeticL2Root254.lean)
identifies that bundle with `gateValue` and `axStackValue`, and proves the
exact dispatch, fetch and read effects. Its
[actual check](results/arithmetic-l2-root254-verification.json) passes four
probes and four typed callers with zero warnings, in 3.859 and 1.742 seconds.
The source retains its 8,192 recursion and 4,000,000 heartbeat limits; the
audit uses defaults. The guard selects 54 project prerequisites from the
checked evaluator and historical enumerator-step result. That older result
has no recorded shared timeout or modern pre-audit object capture; these
limitations and its alternative same-source Cantor object are disclosed in
the [publication](results/arithmetic-l2-root254-publication.json). The new
check selects the evaluator's Cantor object and applies the current policy.
The one-step scheduler theorem is in the following module, despite the
broader description in this source's header.

All eight successful runs use one thread, 4,096 MiB and a shared 120-second source-and-audit
deadline. The first two guards select 35 and 37 exact project prerequisites,
respectively, from already checked parents, with three external source/object
boundaries and Init/Omega. Inputs, first providers and fresh objects are
checked before and after the audit; all reported axioms are standard Lean
axioms. None of these runs rebuilds dependencies or claims to attest the entire
dependency cache.

The [DagRun publication](results/arithmetic-dag-run-publication.json) and
[DagControl publication](results/dag-control254-publication.json) preserve
the source bindings, audits, guards, logs and author history. These are
prerequisites of the remaining scheduler checks. The
[final PA composition](rotation240_pa/final-composition-plan/README.md)
still requires the remaining register and validator dependencies and its
own successful compilation.
