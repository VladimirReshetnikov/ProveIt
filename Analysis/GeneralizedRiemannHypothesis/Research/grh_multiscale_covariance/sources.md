# Source inspection and provenance

Accessed 2026-11-26. The GitHub connector retrieved the root README, compact README, readable GUIDE, recursive tree, and the following source files at the pinned revision `72fead102f663d5c7a407964a13dc0cf9d977207`. The contents were read; the project was not compiled locally.

Repository: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207

| Path relative to repository | Git blob SHA / relevance |
|---|---|
| `README.md` | `fdca72cbfa3557506543b662317267897e0058a0`; scope and reported status |
| `grh/GUIDE.md` | `c2acf9584b58efcb39ac1d668d25c107c3e76a0b`; high-level proof map |
| `grh-compact/README.md` | `85d43d83a7fa3b496968ce9216f4a7d75e44e84a`; statement and build information |
| `grh-compact/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef`; exact Mathlib-facing target definitions |
| `grh-compact/src/Main.lean` | `a5d8389131c985a0b54ce5b0e778ee5c8126a997`; five headline theorems derived from `New.grh` |
| `grh-compact/src/New/Main.lean` | `198ed5bf26aa294898931e0649bc2b88f1389f65`; proof spine, `star_inequality` (line 121), `eventually_primeError_le_rpow` (line 149), `New.grh` (line 174) |
| `grh-compact/src/New/Endgame/PrimeError.lean` | `63eb3d79d95ad815878e623b96f237240058c8e2`; `lambdaClass`, `primeError` (line 38), finite identity (line 60), `isPolar_primeError` (line 69) |
| `grh-compact/src/New/Endgame/OneSidedCriterion.lean` | `93f9a2f5e8cde2438a3cbf030ba823c9613d0ba3`; Landau criterion (line 28), window bound (line 73) |

The repository pins Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its reported standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. Independent verification is documented by Michael Rubinstein at https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ (26 November report: compact edition builds, axiom audit and kernel replay pass, and Comparator paranoid checks accept the reference statements and proofs). This is reported verification, not a claim that this note reproduced the upstream build. No full human review was claimed by upstream.

## Additional reading and novelty check

- https://en.wikipedia.org/wiki/Riemann_hypothesis — formulation, 2026 proof status, consequences, criteria, zero statistics.
- https://andrewodesky.com/rh/overview.html?v=37 — independent outline of the proof's analytic endgame.
- H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory* (2007) — standard analytic inputs.
- D. Koukoulopoulos, *The Distribution of Prime Numbers*, ch. 11 — standard local zero count and logarithmic derivative estimates.
- M. Rubinstein and P. Sarnak, *Chebyshev's bias* (1994) — prime-race limiting distributions.
- G. Martin and N. Ng, *Inclusive prime number races*, https://arxiv.org/abs/1710.00088 — stronger full-support questions and weakened zero independence conditions.
- L. Devin, *Limiting properties of the distribution of primes in an arbitrarily large number of residue classes*, https://doi.org/10.4153/S0008439520000089a — multivariate limiting distribution and support questions.
- W. Banks and K. Loftus, *Unshared zeros of Dirichlet L-functions*, https://arxiv.org/abs/2607.22930 — related zero distinction questions, but the atom argument here does not require that result.

Targeted searches for multiscale/lagged covariance and nondegenerate prime-race covariance without zero independence, shifted explicit-formula prime atoms, and shared zero multiplicities did not identify the precise all-lag/finite-deletion theorem. This is a preliminary novelty check, not an exhaustive literature review. The explicit formula, Hadamard factorization, and limiting mean arguments are classical; the proposed contribution is their combination with isolated shifted prime atoms to establish strict covariance and its consequences.
