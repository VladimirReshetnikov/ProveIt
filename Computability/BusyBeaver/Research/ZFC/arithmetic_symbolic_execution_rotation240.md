# Arithmetic soundness of the Rotation240 symbolic executor

The checked arithmetic mirror now follows the actual `SymbolicRotation240`
executor. Its finite syntax and certificate fuel are external natural data;
register values, gaps, extra spares and execution clocks range over arbitrary
IΣ₁-model elements. Both complete tape halves are preserved.

[`ArithmeticSymbolicStepRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicStepRotation240.lean)
proves literal transitions against the exact 240-state table, affine scans,
normalization and backward box steps. It names four numeric box-operation
contracts in `BoxRuntime`. Literal machine moves supply the positive progress
flag; normalization cannot manufacture it.

[`ArithmeticSymbolicExecutionRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicExecutionRotation240.lean)
proves that erasing the checked mirror gives the actual symbolic step function.
Induction over finite certificate execution then yields numeric machine runs,
including a positive clock for accepted endpoint and halting certificates.
The statements still expose the four `BoxRuntime` fields as a parameter.

[`ArithmeticSymbolicBoxEndpointsRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicBoxEndpointsRotation240.lean)
separately proves all four required contracts using the checked Mark, Increment
and Decrement operations. The permanent spares cover zero decrement at the
last physical register; positive decrement preserves the spare count and
places its extra true cell on the left tape. The right exterior is blank.

[`ArithmeticSymbolicBoxRuntimeRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicBoxRuntimeRotation240.lean)
connects these proofs to all four `BoxRuntime` fields. Its `verifies_sound`
and `verifiesHalt_sound` theorems therefore need only actual finite checker
acceptance and the stated register branch condition; they assume no runtime
contract. This closes the concrete symbolic executor soundness obligation.

Actual checks, all at default proof limits with zero warnings and only
standard axioms:

| Unit | Axiom probes / typed callers | Source / audit seconds | Evidence |
| --- | --- | --- | --- |
| Step | 17 / 17 | 5.533 / 2.568 | [Actual run](results/arithmetic-symbolic-step-rotation240-verification.json) |
| Execution | 9 / 9 | 5.903 / 2.040 | [Actual run](results/arithmetic-symbolic-execution-rotation240-verification.json) |
| Concrete box endpoints | 8 / 10 | 2.679 / 2.350 | [Actual run](results/arithmetic-symbolic-box-endpoints-rotation240-verification.json) |
| Concrete runtime instance | 3 / 7 | 1.722 / 1.832 | [Actual run](results/arithmetic-symbolic-box-runtime-rotation240-verification.json) |

Each source/audit pair shares a 120-second limit, one thread and 4,096 MiB.
The matching artifact directories preserve source plans, audits, raw logs,
guards and actual provider identities. The Step and Execution histories also
retain an independent source/API review. No dependency family was rebuilt.

The checked [instruction runtime](arithmetic_site_rotation240.md) now connects
accepted site certificates to canonical dispatch reentry. Unbounded iteration
and exact startup remain to be joined for the full internal binary simulation.
These checks alone do not prove the PA consistency endpoint.
Machine and framework attribution remains with Mira-Cult, Jeff Ketchersid,
Andrew James Wade and ProveIt.
