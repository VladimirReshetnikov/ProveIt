# Narrow compact symbolic port-bounds helper — source draft

This source-only helper copies the statement and proof of
`C44Short15Facts.port_bounds` into a distinct namespace, with explicit imports
of `CompactMaskBoundFinish`, `CompactSymbolicPorts`, and
`ArithmeticStandardCasts`. The proof body is byte-identical to the current
source theorem. It retains the model `IΣ₁` context, B/K/L/H parameters,
exact beta identity and exact symbolic low/high mask equalities. K remains
arbitrary; the four conclusions are beta positivity, low<beta,
beta+high<2beta, and beta≥46.

The existing graph chain is unchanged. A future replacement would have to
substitute four explicit imports and six theorem references, then verify every
source interface and transitive provider/companion route. A line-parsed
read-only route comparison indicates removing the existing heavy direct import
reduces its extra qualified source closure by 74 modules; it does not prove
that the new helper compiles or that its imports are available coherently.
No Lean run, preflight, provider or iPRA endpoint claim is made.

Independent source review: [compact port-bounds slim](../../reviews/ordinary14-compact-port-bounds-slim-independent/README.md).
