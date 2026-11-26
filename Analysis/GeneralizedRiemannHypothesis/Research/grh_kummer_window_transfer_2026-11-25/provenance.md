# Source provenance and scope

Accessed 25 November 2026 (Pacific date) using the GitHub connector. No repository modifications were made. The public repository's recursive tree endpoint returned `72fead102f663d5c7a407964a13dc0cf9d977207`, not truncated. The connector returned the following exact file blob SHAs. The readable edition was not separately audited. The root README reports machine checks, not human review; the compact README reports the pinned build and comparator runs. We inspected source, not local Lean execution (Lean is unavailable and direct network access was disabled in the container).

| Path in https://github.com/lsernau/grh-lean | Blob SHA-1 | Use |
|---|---|---|
| README.md | fdca72cbfa3557506543b662317267897e0058a0 | Scope, status |
| grh-compact/README.md | 85d43d83a7fa3b496968ce9216f4a7d75e44e84a | Five statements, reported kernel checks, pinned Mathlib |
| grh-compact/GUIDE.md | ca70306f0ee22fca325f7f515667e51625e8eabd | Three main inputs, parameters |
| grh-compact/Challenge.lean | 4230ff8fe8b0265a44db348c22cd5f03a7c3f3fe | Comparator challenge only (not imported) |
| grh-compact/scripts/PrintAxioms.lean | ec5adcfd7baeff36130db9a763720ba1a6567c57 | Axiom audit script |
| grh-compact/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Exact Mathlib endpoint types |
| grh-compact/src/Main.lean | a5d8389131c985a0b54ce5b0e778ee5c8126a997 | Endpoint proof wrappers |
| grh-compact/src/New/Main.lean | 198ed5bf26aa294898931e0649bc2b88f1389f65 | star_inequality, eventually_primeError_le_rpow, New.grh |
| grh-compact/src/New/Endgame/PrimeError.lean | 63eb3d79d95ad815878e623b96f237240058c8e2 | primeError, isPolar_primeError |
| grh-compact/src/New/Endgame/OneSidedCriterion.lean | fetched in full (SHA not recorded) | entireL_ne_zero_of_primeError_le, IsPolar.eventually_moment_le, IsPolar.exists_window_sub_mul_le |
| grh-compact/src/New/Lift/CokernelKillers.lean | ba8a479cecd29393b86e3f320991c20baf108487 | Sample local lifting mechanism; inspected excerpts |

The source map is descriptive, not a complete dependency audit. The main source and endpoint types were read; the source's large library of supporting proofs was not reviewed declaration by declaration. Upstream compact README reports Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Previous reports

Listed the directory https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming. Its README (2433 lines at access) did not contain GRH/Riemann/Alpöge matches; the actual directory contained 19 GRH-related ZIP files. We decoded ZIP central directories and selected README, report, and evidence text in the connector execution environment using raw DEFLATE. We reviewed extracted excerpts and section headings, not all reports in full. No earlier computation was independently rerun. In particular:

| Archive | Reviewed scope |
|---|---|
| grh_transfers.zip | Exponent-six classification; fixed-window mod-4 prime race; degree-two zero sums; cubic zero detector. |
| grh_sylow_transfer_2026-11-25.zip | General Sylow-filtered nonabelian detector; PSL(2,7) two-pattern test; comparison still missing; uses [t,t²] window. |
| grh_method_transfers_2026-11-25.zip | General periodic Frobenius obstruction; root-count and fourth-power sampling; explicit cubic discriminant -23 target; Kummer effective splitting noted. |
| grh_method_transfers_2026-11-25(1).zip | Torsion-selection, ramification and census restrictions; prior-report survey notes Kummer/Hooley scope. |
| grh-arithmetic-transfers.zip | Progression windows, divisibility, additive questions, isogeny uniformity, one-sided Dedekind criterion. |
| grh_relative_prime_races_2026-11-25.zip | Relative zeta, normal towers, S4, mixed composita, arithmetic obligations. |
| grh_transfer_analysis_2026-11-25.zip | General one-sided Laplace criterion, auxiliary family, classical consequences, source audit. |

The connector returned no bytes for the 2.9 MB `grh_beyond_dirichlet_grh_2026-11-25.zip` in one attempted base64 fetch. Other unreviewed ZIPs were not audited. Accordingly, no assertion of complete novelty relative to the incoming directory is made. The selected topic differs from the principal findings of the inspected excerpts, but individual pieces are classical or may overlap with earlier reports.

## Literature

- Masatoshi Suzuki, *On variants of Chebyshev's conjecture*, Ramanujan J. 68 (2025), 95, https://doi.org/10.1007/s11139-025-01238-9 — precedents for one-sided weighted prime-sum detectors.
- C. Hooley, *On Artin's conjecture*, J. Reine Angew. Math. 225 (1967), 209–220 — conditional primitive-root sieve.
- Pieter Moree, *Artin's primitive root conjecture — a survey*, https://arxiv.org/abs/math/0412262 — classical sieve and uniform effective split-prime count. The present argument uses a fixed cutoff followed by a limit rather than a growing squarefree cutoff; no priority claim for that observation.
- Steve Fan and Paul Pollack, *Counting primes with a given primitive root, uniformly*, Mathematika 71 (2025), e70055, https://doi.org/10.1112/mtk.70055 and https://arxiv.org/abs/2505.05601 — effective split-prime estimate and modern context.
- H. Montgomery and R. Vaughan, *Multiplicative Number Theory I* (2007), classical Landau theorem and Brun–Titchmarsh. J. Neukirch, *Algebraic Number Theory* (1999), Artin factorization and class field theory.

The literature search was targeted, not exhaustive. We do not claim to have resolved nonabelian GRH, Artin's conjecture, or another named open conjecture. The precise new arithmetic obligation in report.tex is conditional and is not shown by the inspected Lean sources.
