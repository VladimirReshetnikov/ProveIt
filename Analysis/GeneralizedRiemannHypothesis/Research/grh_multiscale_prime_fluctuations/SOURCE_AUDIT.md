# Source audit (26 November 2026)

GitHub connector retrieved the repository metadata, recursive `main` tree, root README, compact GUIDE/README, and portions of the sources below. The recursive tree's **tree** SHA (not asserted to be a commit SHA) was `72fead102f663d5c7a407964a13dc0cf9d977207`. `main` is the default branch. No complete checkout or build was performed.

| File (under `grh-compact/`) | Blob SHA when recorded | Relevant declaration / content |
|---|---|---|
| `src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | DirichletLNonvanishingRightOfHalf; DirichletLZerosOnLine; PrimitiveDirichletLZerosOnLine |
| `src/Main.lean` | `a5d8389131c985a0b54ce5b0e778ee5c8126a997` | riemannHypothesis; LFunction_eq_zero_re |
| `src/New/Main.lean` | `198ed5bf26aa294898931e0649bc2b88f1389f65` | star_inequality; eventually_primeError_le_rpow; proof-spine comment; inspected first 170 lines |
| `src/New/Endgame/OneSidedCriterion.lean` | `93f9a2f5e8cde2438a3cbf030ba823c9613d0ba3` | entireL_ne_zero_of_primeError_le; IsPolar.exists_window_sub_mul_le; inspected first 200 lines |
| `src/Lib/Analytic/Landau/PolarLandau.lean` | not recorded | IsPolar.landau; sign of real residues; Laplace transform; inspected excerpt |
| `README.md`, `GUIDE.md` | not recorded | reported build configuration and checks; proof architecture |
| `Challenge.lean` | not recorded | statement-only comparator challenge (uses sorry intentionally and is not imported in the proof) |

Repository: https://github.com/lsernau/grh-lean

The compact README reports successful Lean replay and standard axioms only. The root README explicitly says no mathematician had read the proof through. These are reported checks, not checks independently executed for this project. The Mathlib statement covers Dirichlet characters, including imprimitive ones. No broader automorphic GRH is assumed.

## Web sources and novelty assessment

- https://en.wikipedia.org/wiki/Riemann_hypothesis (accessed 26 November 2026): formulation, reported formal proof and endorsements, prime counting and explicit formula.
- https://doi.org/10.1007/s11139-025-01238-9 (Suzuki 2025; correction https://doi.org/10.1007/s11139-025-01289-y): prior sign criteria for weighted von Mangoldt functions.
- https://doi.org/10.5281/ZENODO.24447004 (Dumas, 23 November 2026), read via https://www.academia.edu/181622923/The_Riemann_Hypothesis_in_One_Inequality_for_Least_Common_Multiples: extremely close precedent on dyadic lcm ratios, one-sided exponents and local filters for RH. Do not claim the q=1 dyadic statistic as novel. The all-modulus, all-positive-moment, odd-filter and sharp critical mean/series results are the proposed extensions. The Dumas preprint was not independently checked in full.
- https://www.cs.uleth.ca/~akbary/limitingdistributionFINALQJM.pdf (Akbary, Ng, Shahabi; search-result abstract consulted): prior limiting distribution framework.
- https://dlmf.nist.gov/25.16 (classical explicit formula and RH equivalent error bound).

Queries included one-sided smoothed Chebyshev function, dyadic differences, LCM ratios, Riesz means, Landau, almost periodic limiting distributions. The search was targeted, not exhaustive; novelty is a candidate, not a certification of priority. The report's mathematical claims are deductions from stated classical inputs, independent of the machine checks. The critical claims specifically assume Dirichlet GRH(q).
