# Forty-nine-variable quartic candidate

This exploratory 185-operation graph starts from the 50-variable rank-seed
candidate and replaces its two positive coordinates for the signed value `Q`
with a single positive `Q` coordinate, removing the subtraction gate. The
strong-square residual forces `Q` to be the square of a positive scaled-index
variable at a zero. The [combined model proof](../adaptive-combined49-model/README.md)
binds the exact graph to Lean and composes the direct-`Q` and rank-seed
reductions at the fixed ports in every IΣ₁ model. Its paired model replay passed
on a historical provider; inherited ancestry remains qualified there.

`generate.py` constructs the graph from the pinned parent and checks gate and
input liveness. `verify_degree.py` expands the 35 residuals as exact sparse
polynomials and checks degree four after the positive shift. The leading
quadratic residual coefficient is port-independent and nonzero. This degree
calculation is external to Lean.

The exact shifted fixed-port literal has a no-premise [native endpoint](../../Lean/DiophantineConsistency/IPRANamedValues49Native.lean).
The [focused guarded comparison](../../reviews/ipra-named49-native-verification/README.md)
matched seven rows and 11,762 files. It uses the mapped Foundation refutation
predicate; its interpretation as Con(ZFC) relies on the separate interpretation
and refutation bridge. The historical provider, author-only 848-module ancestor,
and inherited package-transitive and dynamic-import ancestry remain
qualifications. No global minimality claim is made.

The [base-10 presentation](../../equation4-49.pdf) has separately named
positive variables. `generate_equation4_49.py` constructs it and
`verify_display4_49.py` checks all definitions and residuals against the graph,
including mutation controls. Two PDF builds were byte-identical, with SHA-256
`43f13a2fda13794ae13e8a4aafafbd113b32329a9f4efd3e8113b9e8c6333aec`.
