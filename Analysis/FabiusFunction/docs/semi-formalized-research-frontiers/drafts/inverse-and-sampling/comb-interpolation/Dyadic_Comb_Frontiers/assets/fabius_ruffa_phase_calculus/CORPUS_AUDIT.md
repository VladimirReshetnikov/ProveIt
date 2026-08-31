# Corpus audit and novelty boundary

## Snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Audited path: `Analysis/FabiusFunction/docs`, recursively
- Commit: `95d545d012b520df78ca2d841e4d93cba79e3f50`
- Snapshot date: 2026-08-28
- Recursive inventory: 95 `.tex` paths

The repository manifest says that current consolidated frontier volumes are the authoritative layer and that many older directories are archived source history or assets absorbed into those volumes. The audit therefore used the manifest and provenance appendices to avoid counting duplicate drafts as independent prior art.

## Sources read most closely

The main exposition and the relevant consolidated volumes were read in full or theorem-by-theorem:

- `Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
- `semi-formalized-research-frontiers/drafts/inverse-and-sampling/Dyadic_Comb_Frontiers/Dyadic_Comb_Frontiers.tex`
- `semi-formalized-research-frontiers/drafts/integration-and-transforms/Integration_and_Transform_Frontiers/Integration_and_Transform_Frontiers.tex`
- `semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/Up_Polynomial_Synthesis.tex`
- the current exponent/q-series, inverse/sampling, representation, and Thue–Morse consolidation sources identified by `drafts/MANIFEST.md`
- `PAPER_COVERAGE.md`, for the boundary between proved Lean declarations, source-paper claims, and open frontier material

All remaining active and archived `.tex` paths were inventoried and searched for Euler–Maclaurin formulas, shifted combs, first-failure aliases, phase superconvergence, Richardson extrapolation, moment formulas, root-of-unity filters, and Ruffa/exhaustion terminology.

## Results treated as repository baseline

The report does **not** claim novelty for:

- exact unshifted dyadic-comb sums for `x^p F(x)`, their finite Euler–Maclaurin corrections, spectral Dirichlet first defects, and repeated-sum reductions;
- full-support shifted Rvachev moment cubature, generalized lattice/Strang–Fix order, first-failure alias series, and polynomial-reproduction connections;
- Bell–Bernoulli moment and cumulant formulas and the reduction of `I_p` to moments of `F'`;
- generic Richardson and q-binomial acceleration, or the already developed phase/resolution tomography viewpoint;
- the repository’s extensive fractional/complex-order integral-transform theory.

## Main claims developed in the new report

Relative to the audited corpus, the report proves and emphasizes:

1. a one-sided shifted Fabius Poisson–Euler–Maclaurin identity for arbitrary integer panel count, with a finite Bernoulli endpoint polynomial and a superalgebraic alias remainder;
2. exact collapse for every phase when `ν₂(M) ≥ p+1`, with the odd part of `M` unrestricted;
3. a coherent shifted radix-`b` exhaustion formula whose layer is a residue-class/root-of-unity filter and whose even-radix Fabius tail becomes finite after a calculable level;
4. the complete first-defect phase zero set for every `M = 2^p q`, `q` odd, proved from the new relative product inequality `|Φ(πqℓ)| ≤ |Φ(πq)|/|ℓ|`;
5. exact integration in the phase parameter, including finite Simpson, Boole, and Gauss phase cubature for Fabius moments;
6. exact Thue–Morse, root-of-unity, and arbitrary-order digit-mask annihilation formulas for Bernoulli phase modes;
7. multidimensional exact Ruffa shells and tails obtained by tensorizing the finite one-dimensional correction.

Novelty language in the report is deliberately relative to this repository snapshot, not an unqualified claim of priority over all mathematical literature.
