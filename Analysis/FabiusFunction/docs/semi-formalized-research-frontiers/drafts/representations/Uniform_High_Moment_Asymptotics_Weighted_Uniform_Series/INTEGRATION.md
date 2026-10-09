# ProveIt integration notes

## Placement

Suggested new directory:

```
Analysis/FabiusFunction/docs/research/UniformMomentAsymptotics/
```

Preserve the `code/` and `data/` relative paths used by the TeX source.
No changes to the root import surface, Lake configuration, or existing theorem
statements are required. Add a link to the Fabius research inventory only after
review. The new directory name is a suggestion, not a claim that it exists.

## Relationship to inspected repository material

`Analysis/FabiusFunction/Lean/FabiusFunction/EndpointLaplaceComparison.lean`
already exposes an endpoint-to-Laplace comparison and a normalized second
moment correction. `LaplaceMomentBounds.lean` supplies quantitative tilted
moment estimates and makes certain Fabius comparisons unconditional. Those
existing ideas are credited in article Section 1.

This manuscript instead proves array-uniform estimates at a self-consistent
tilt, develops the gamma smoothing identity to all fixed orders, identifies
fixed-geometric cancellation improvements, and proves a uniform crossover
criterion. It is not a claim that an existing Lean bound has been replaced.
The full repository research corpus was not exhaustively audited for duplicate
or stronger results; review the precise theorem statements before naming them
as new public API endpoints.

## Normalization bridge

The manuscript uses the probability moment

```
M_n = E[X^n] = E[(1-X)^n],    X = sum_{j>=0} 2^(-j-1) U_j.
```

For the standard Fabius CDF on `[0,1]`,

```
F(2^(-n)) = 2^(-n(n-1)/2) M_n / n!.
```

Do not identify `M_n` directly with a repository half-moment or a moment of the
centered Rvachev function without proving the appropriate factor and index
shift. In particular, distinguish cumulants at tilt `n` from those at the
saddle `t_n`.

## Suggested formalization order

First prove the single-summand estimates, finite-array moment recurrence,
mean/variance mesh brackets, and the global crossover bound. Then extend to
countable arrays and the exact gamma Fourier identity. The all-orders theorem
requires uniform analytic remainder estimates and should be a separate phase.
The exact C1, C2-gradient, and gamma-line identities can be finite algebraic
checks once the coefficient recursion has formal semantics.

No Lean build was run for this package. Follow the project's current build
instructions: one leaf module per invocation, with no parallel build launches.
Do not introduce `sorry`-based files into a purported checked theorem boundary.

## Reproduction

Run `make check`, `make tables`, and `make pdf` from this directory. The package
uses only Python dependencies declared in `requirements.txt`; no source code
from OpenAI Math is needed for these proofs or computations. The provenance
ledger records inspected sources without asserting a common repository commit
for observations made at different times.
