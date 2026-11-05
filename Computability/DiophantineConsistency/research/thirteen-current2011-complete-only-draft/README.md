# Thirteen-variable completion-only diagnostic

This source retains the factored `complete` theorem with its original
statement, but removes the subsequent reverse bridge and iPRA endpoint
declarations. It imports the same separately checked ring-invariant and
rank-ordinate helpers. It is an isolated diagnostic, not a checked proof.

Actual outer session 35336 exited 1: the dependency run succeeded, but Lean
compilation exited -6 after 6.97 seconds with the same interpreter memory
exception at `-M2800`. The full [state](attempt01/state.json) has SHA-256
`e3a4c8a43bef25e1f5cdbf4a801f1ba6eb6b0f23f22b737b773d8ba02b11b3e1`;
the source SHA-256 is
`6188f27280f4bf958c846b7550ae1d4a40487bd929d2d5bb29c6e4d86d0dccd6`;
the runner SHA-256 is
`5ca78119ff2308d45b947e373f3a1a6f73b91318190dbbf8ba780a2ccbd66aec`.
Removing the later bridge and endpoints did not make this source compile at
the cap. This does not locate the precise operation or show a mathematical
error. The run used one worker, a 180-second GNU foreground timeout and
resource prechecks; it had no automatic group-RSS or host-memory stopping.
No completion or iPRA endpoint result is claimed.
