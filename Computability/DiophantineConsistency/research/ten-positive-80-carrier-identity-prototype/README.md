# Exact 80-row carrier identity

`Direct80CarrierIdentity.lean` exposes the exact graph's transport factor `B`, correction `Kpos`, signed offset `e`, and scaling expressions as Lean syntax. It proves by definitional equality that the actual `z` and `m` fields of `Direct80Graph.graph` have the displayed carrier shapes, and proves their evaluations over every commutative ring. No graph-zero, positivity, sign, or fixed-port assumption is involved.

The guarded author check `observations/attempt02/` passed without diagnostics, yielding `/tmp/tenpositive-80carrier-identity-2hfpzucj/Direct80CarrierIdentity.olean`, SHA-256 `c13089b048fa33eb8d0e2729d46f702e1bae13b1846b3ec6eeb250c8ca0c29a6`; attempt01 failed from a redundant tactic after the goal had already closed. Printed Lean axiom is `propext`. The runner pins selected prototype objects and one inherited provider, not complete transitive project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed. External JSON-to-Lean and displayed-file bindings are separate boundaries.

This is an exact ring identity only; plugging it into the conditional transport inequality, obtaining the integral signed carrier and one-sided bounds, and proving graph-to-halt or an iPRA endpoint are separate tasks.
