# Source audit (2026-11-26)

Repository: https://github.com/lsernau/grh-lean
Revision confirmed by GitHub commits/main: `72fead102f663d5c7a407964a13dc0cf9d977207` (2026-11-25 20:38:07 UTC).

Inspected root README, compact README and GUIDE, and the following source files through the GitHub connector. Blob identifiers are recorded for reproducibility.

| File relative to grh-compact | Blob SHA | Role |
|---|---|---|
| src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Mathlib-only theorem statements |
| src/Main.lean | a5d8389131c985a0b54ce5b0e778ee5c8126a997 | exports five theorems |
| src/New/Main.lean | 198ed5bf26aa294898931e0649bc2b88f1389f65 | star_inequality; eventually_primeError_le_rpow; New.grh |
| src/New/Endgame/OneSidedCriterion.lean | 93f9a2f5e8cde2438a3cbf030ba823c9613d0ba3 | window selection using moments; Landau criterion |
| src/New/Endgame/PrimeError.lean | 63eb3d79d95ad815878e623b96f237240058c8e2 | lambdaClass; primeError; isPolar_primeError |
| src/Lib/Analytic/Landau/PolarLandau.lean | 6b80c9062a74ecadcd9c51f9459cb3c71ac2ded9 | IsPolar, Laplace powers, Landau lemma |

`Challenge.lean` is a statement-only Comparator fixture containing `sorry`; the README explicitly says it is not imported by the build. We did not audit every dependency or execute Lean. The reported proof status is corroborated by https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ (independent verification reports), and the current RH overview at https://en.wikipedia.org/wiki/Riemann_hypothesis. The new mathematical result uses Dirichlet GRH as a named theorem, with no additional hypothesis about zero simplicity, ordinate independence or central nonvanishing.

Targeted literature search: https://arxiv.org/abs/1710.00088 (inclusive prime number races); https://arxiv.org/abs/2607.22930 (unshared zeros of Dirichlet L-functions); https://dlmf.nist.gov/25.15 (standard analytic facts). This is a limited search rather than a claim of priority.
