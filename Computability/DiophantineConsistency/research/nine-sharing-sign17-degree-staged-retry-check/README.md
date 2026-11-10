# Sign17 staged degree explicit-composition retry

Eleven source-only stages propose remaining shared-node and residual bounds
and the arbitrary-port Fin17 polynomial degree upper bound ≤96. The generated
node proofs now use explicit compositional `change` expressions with previously
bounded shared nodes as leaves, avoiding the earlier no-progress simp path.
The audited five-node probe and the same monitored resource limits remain. No
full degree theorem, exact lower, external binding or iPRA result is claimed
before Lean and independent audit.

Author no-Lean preflight exited 0. Runner SHA-256:
`553d568f8c178f109b30146c746f255db52b051c5d636bbb1f6951360dad2312`;
manifest SHA-256:
`995cda859a86e037d2f4dffbce73ec8634e06c8903ab1f3e05d8e836ab7cec80`.
The [independent prelaunch audit](../../reviews/nine-sharing-sign17-degree-staged-retry-prelaunch-independent/README.md) passed. Attempt 01 completed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-degree-staged-retry-terminal-independent/README.md) passed; the packet is frozen.
