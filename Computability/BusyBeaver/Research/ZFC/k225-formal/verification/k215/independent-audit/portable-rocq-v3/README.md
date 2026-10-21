# Portable Rocq driver: repaired successor

Full source review of held driver `bb810279f5fb62fb7b6c78da5f32fbea312f3e0ad05fefa0258da9e0d87898fc` resolves all three findings from the [preserved first review](../portable-rocq-v1/README.md). No further actionable issue was found for the stated private-output, same-toolchain, serial-build workflow.

- Endpoint assumption failures are recorded as `FAIL_ASSUMPTIONS`; reuse requires successful status, unchanged inputs, the exact object and saved log, and a fresh evaluation of the two-Closed/no-Axioms gate.
- The immutable toolchain boundary now includes compiler, checker, worker and installed library objects. Its hash is recorded in module and recursive-check receipts; changing it rejects resume without overwriting the old boundary.
- SIGTERM is converted into an exception handled by process-group termination and waiting. Signals are blocked only across spawning, then the original mask is restored in both child and parent. The intermediate control's inherited-mask delay remains disclosed as history.

Independent text comparison confirms unchanged source-selection and plan generation; the selected 237-module order, canonical source paths and dependency edges still match the actual build plan. The recursive `coqchk` argv and its absence of admit/norec flags are unchanged.

The author supplied eight passing fake-log/process controls, including a disposable child/grandchild SIGTERM test. This reviewer read their source and results and verified the held-driver binding, but did not rerun them. The controls are not proof checks. The [receipt](review.json) and exact reviewed driver/diff are preserved here. The actual proof supervisor remains separately running; this review asserts no final proof, endpoint-assumption or recursive-kernel outcome.
