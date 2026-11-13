# Sign17 univariate-degree compatibility probe

One source-only stage proposes univariate product/dominant-addition facts and
a bound from a one-variable multivariate polynomial to its image under the
unique-variable equivalence. It explicitly imports and pins the Mathlib
MvPolynomial.Equiv object; source-graph inspection found no path from that
module to the previously conflicting Matrix.Defs, but actual compatibility
remains for Lean to check. The audited staged-upper provider and bounded
resource guards are retained. No sign17 lower/exact degree or external binding
is claimed.

Author no-Lean preflight exited 0. Runner SHA-256:
`e84630d7da922fbf8388ba58550833eb8df4b28fa70bcbd5d8e97b04786b18aa`;
manifest SHA-256:
`6bd41d6d4ca465d1dcc662617b75b7048edf70025cb0cd1e05b85c9b133a4694`;
explicit Equiv object SHA-256:
`fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-univariate-degree-probe-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-univariate-degree-probe-failure-independent/README.md) passed; the packet is frozen.
