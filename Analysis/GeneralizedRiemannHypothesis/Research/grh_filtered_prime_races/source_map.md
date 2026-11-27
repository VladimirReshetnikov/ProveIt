# Source map and scope of inspection

Access date: 2026-11-26. GitHub connector used to fetch the repository metadata, tree, README, and selected files. The research note is based on the following revision:

- Repository: https://github.com/lsernau/grh-lean
- Commit: `72fead102f663d5c7a407964a13dc0cf9d977207`
- Pinned tree: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
- Upstream license: Apache-2.0. No upstream proof source is redistributed here.

## Inspected files

Paths below are relative to the pinned tree. Blob IDs are from the connector's responses.

| Path | Blob ID | Role |
|---|---|---|
| README.md | fdca72cbfa3557506543b662317267897e0058a0 | Editions and reported machine checks, build requirements, status |
| grh/GUIDE.md | c2acf9584b58efcb39ac1d668d25c107c3e76a0b | Readable proof map, names, logarithmic scale machinery |
| grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Statement scope, independent checks, comparator, dependency layout |
| grh-compact/README.md | 85d43d83a7fa3b496968ce9216f4a7d75e44e84a | Compact edition and main theorem names |
| grh-compact/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Mathlib-only statement interface |
| grh-compact/src/Main.lean | a5d8389131c985a0b54ce5b0e778ee5c8126a997 | Five exported theorems |
| grh-compact/src/New/Main.lean | 198ed5bf26aa294898931e0649bc2b88f1389f65 | Main inequality and final nonvanishing steps (selected declarations) |
| grh-compact/src/New/Endgame/PrimeError.lean | 63eb3d79d95ad815878e623b96f237240058c8e2 | `lambdaClass`, `primeError_eq_sum`, `isPolar_primeError` |
| grh-compact/src/New/Endgame/OneSidedCriterion.lean | 93f9a2f5e8cde2438a3cbf030ba823c9613d0ba3 | `entireL_ne_zero_of_primeError_le`, `IsPolar.exists_window_sub_mul_le` |
| grh-compact/src/Lib/Analytic/Landau/PolarLandau.lean | 6b80c9062a74ecadcd9c51f9459cb3c71ac2ded9 | `IsPolar`, `laplace_pow`, `LSeriesHasSum_mul_vonMangoldt`; first 60 lines inspected |
| grh-compact/src/New/Endgame/LongForms.lean | 9eff36cf003ac398fbd24361e80e95a03d0b0e05 | Arithmetic side of main inequality; first 60 lines inspected |

Use `https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/` followed by a path to retrieve the source.

The exact exported GRH interface `LFunction_eq_zero_re : DirichletLZerosOnLine` asserts that all zeros of all Dirichlet characters in the open critical strip have real part one half. `LFunction_ne_zero_of_half_lt_re` gives the corresponding right-half-plane nonvanishing with the principal-pole exception. `riemannHypothesis` supplies the zeta statement. No assumption of simple or linearly independent zeros occurs in the interface. The new proofs here are based on this interface and classical analytic facts, not on an unverified claim about arbitrary automorphic L-functions.

The ramp used in the new paper is the unnormalized kernel x/n-1. The normalized upstream `primeError` uses the related kernel 1/n-1/x and removes main terms using a log-derivative constant. We retain the full vector of residue classes, use Fourier orthogonality, and design an averaging polynomial that kills both main terms and central zero frequencies. The new Hadamard shift argument handles exact zero collisions across characters. These constructions are not claimed to be part of upstream code.

## Other inspected references

- https://en.wikipedia.org/wiki/Riemann_hypothesis — formulation, proof status and implications for prime distribution.
- https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ — joint Lean FRO/Mathlib verification statement for Alpöge's RH proof.
- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ — independent verification logs including the shortened proof.
- https://arxiv.org/abs/1710.00088 — Martin and Ng, inclusive prime races with linear-independence conditions.
- https://doi.org/10.4153/S0008439520000089 — Devin, multidimensional limiting distributions and prime races.
- https://matwbn.icm.edu.pl/ksiazki/aa/aa28/aa2847.pdf — Fujii on coincidence of zeros (search result abstract/text only; not a PDF layout analysis).
- https://arxiv.org/abs/2607.22930 — Banks and Loftus, unshared zeros; a different question about values of L-functions at zeros.

Searches also included variants of `Dirichlet L-functions linear independence zero multiplicities logarithmic derivative finite poles gamma shift`, `smoothed prime races convex hull support linear independence zeros positive definite covariance`, and `prime race almost periodic smoothed prime counts sign changes bounded gaps logarithmic scale`. The searches are not an exhaustive priority check. The paper cites standard textbooks for classical analytic inputs.

## Checks not performed

No full upstream build, Lean kernel replay, or new Lean formalization. No numerical calculation of actual zero multiplicities, their coincidences, or certified eigenvalues of the limiting covariance. The script's independent quadrature checks and finite samples were executed; these establish only numerical consistency of the computational illustration. No repository writes were made.
