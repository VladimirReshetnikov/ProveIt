# Scoped comparison with late arrivals 160--165

Read 25 October 2026, after the new 218- and 220-variable equations had been constructed.

This comparison is frozen at ProveIt commit `897ee2b513fae1e802575abc9f8b6fae896b5014`. It covers the six newly placed package READMEs, not a fresh replay of their full certificates. The table records their reported direct unrestricted-integer endpoints; it is not an independent certification of those endpoints.

| Package and profile | Integer variables | Quadratic rows | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| 160, minimum dimension | 237 | 173 | 14,129 | 7,968 |
| 160, principal | 238 | 174 | 5,479 | 7,968 |
| 161, fewer variables | 238 | 174 | 12,789 | 7,968 |
| 161, affine-horizon alternative | 237 | 173 | 12,787 | 1,298,074,204,962,300,530,359,575,779,475,468 |
| 162, principal | 236 | 173 | 4,876 | 7,968 |
| 162, dense companion | 235 | 172 | 12,566 | 7,968 |
| 163, self-power sparse | 236 | 172 | 4,992 | 10,722 |
| 163, self-power dimension | 235 | 171 | 10,536 | 10,730 |
| 163, shared-error | 234 | 171 | 21,385 | 44,800 |
| 164, integer dimension | 239 | 175 | 12,658 | 6,144 |
| 164, integer balanced | 240 | 176 | 5,232 | 4,096 |
| 164, integer sparse | 240 | 176 | 4,927 | 7,596 |
| 165, balanced principal | 238 | 175 | 5,236 | 3,968 |
| 165, dimension tradeoff | 237 | 174 | 18,569 | 7,680 |
| 165, factorial-free branch | 239 | 175 | 5,137 | 3,968 |

All these listed direct equations have reported degree four. Package 161's high-height alternative is retained in the table to avoid conflating its smaller dimension with its modest-height principal.

The new 220-variable equation has 157 rows, 7,793 monomials and height 45,161. The new 218-variable equation has 155 rows, 14,410 monomials and height 5,023,040. Therefore no unrestricted-integer endpoint reported by these six READMEs duplicates or dominates either new equation: each uses at least 234 variables and 171 rows. Conversely the new equations do not uniformly dominate the late arrivals, which often have substantially lower coefficient height and smaller support.

The precise all-metric improvement remains the comparison of the new 220-variable equation with its actual pooled225 parent: 225 to 220 variables, 162 to 157 rows, 7,867 to 7,793 monomials, and height 128,446 to 45,161, all at degree four. The 218-variable result remains a separate dimension tradeoff.

Package 164 also reports a 206-variable quartic over **nonnegative** integers, with 158 rows, 8,210 terms and height 130,686,376. Its domain differs from unrestricted integers. It must not be silently treated as either a counterexample to the new unrestricted count or an unrestricted-integer equation. The same package includes 207- and 208-variable nonnegative companions.

The small-variable native-coefficient circuits and the height-one quartics in these arrivals address different comparisons. None supports a global variable-count or global simplicity claim for the new direct construction.

## Method overlap

Package 163 explicitly uses six common-Hessian projections per direct branch. This agrees with the mechanism already described in package 159. Accordingly, the new contribution should not claim invention of common-Hessian projection. Its concrete achievement is applying and combining integral reductions on the newly pooled225 parent, giving new complete 220- and 218-variable polynomials and exact restoration certificates.

The late arrivals add affine horizon and signed-bootstrap reductions, strict-horizon factorial-free variants, an unsquared-factor natural source, wider remainder budgets, and compact norm improvements. Their ordinary arithmetic source changes are not part of the newly certified algebraic projection. Composing them with the new pooled parent is a further research direction and would require separate completeness and dependency proofs.

No additional moving-head check is needed for this frozen comparison. A later repository state can be assessed in a subsequent iteration without changing the pin or historical evidence used here.
