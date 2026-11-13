# Sign24 exact Lean polynomial degree client draft

This source-only client proposes combining the checked sign24 abstract
expression degree upper bound with the independently audited lower bound, obtaining
total degree exactly eight for any integer port vector and for current ports.
The [guarded client](../nine-sharing-sign24-exact-degree-check/README.md) has
now compiled and passed an independent terminal audit after checking both
provider objects and their byte-compatible overlays. The source header's
`SOURCE-ONLY` label predates that checked exact snapshot.

Even a successful theorem concerns the symbolic Lean expression and its
`Expr.toPolynomial`, not external JSON/port-byte or PDF semantics, a literal
decimal export or a nine-variable Jones applicability theorem.
