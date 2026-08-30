# Corpus audit and novelty boundary

## Repository boundary

- Repository: `VladimirReshetnikov/ProveIt`
- Subtree: `Analysis/FabiusFunction/docs`
- Pinned commit: `21758aba2f8e200342be2a7b321247dac80efc00`
- Pin date: 2026-08-28
- Recursive source inventory at audit time: 95 paths with extension `.tex`

The documentation tree contains canonical expositions, imported papers, historical revisions, a consolidated frontier volume, and thematic draft consolidations. To avoid counting archived copies of the same theorem as independent sources, the audit followed the repository's consolidation policy:

1. inventory every `.tex` path recursively;
2. use the canonical exposition and consolidated frontier volume as the current mathematical spine;
3. inspect the live draft manifest and all topic-specific sources overlapping finite sinc products, splines, Thue–Morse formulas, `q`-Richardson acceleration, transport, information geometry, or multiresolution analysis;
4. normalize archived versions against their live successor;
5. run formula- and phrase-level searches for the proposed exact invariants.

In the report, “proved here” means that no explicit counterpart was located in this pinned corpus after this cumulative audit. It is not a claim of exhaustive worldwide priority.

## Established inputs excluded from novelty claims

The audit found that the corpus already contains:

- the random-uniform-series construction of the Fabius/Rvachev law;
- finite convolution and Thue–Morse truncated-power spline formulas;
- exact supports, knots, smoothness, refinement identities, and dyadic arithmetic;
- finite and infinite sinc products, Fourier inversion, zero structure, and decay;
- all-orders `4^{-N}` deconvolution expansions with Bell/Bernoulli coefficients;
- signed zero-preserving `q`-Richardson acceleration;
- lower-Lambert endpoint transseries and inverse-Fabius phase analysis;
- Haar, Faber–Schauder, Bernstein/Kummer, and related multiresolution representations.

Those results are used as baseline rather than relabeled as new.

## Overlap-critical source hashes

The four directly materialized sources most likely to overlap the new theorem package had these SHA-256 hashes:

```text
c2f203778b1889bff22e4839f369c16e50e9ef45799717f6f1357dc1df3f40d1  Fabius_Function_and_Rvachev_Up.tex
32953767492749ce7668a28896e76075ab3ab1f9c42f370c4e31e35638f21857  fabius-frontier-results.tex
832c790e8bd247ea1569c7ef1ac09017a9c083d7c8f5ed17d57035e2aa82175c  Fabius_Rvachev_Multiresolution_Representations.tex
81a0a911ac7ab28e12c6b87ccaf76ffccaf32e48f873abff18fb7a2d01bcf3e5  Fabius_Dyadic_q_Connections.tex
```

## New package isolated by the audit

The report proves a linked package centered on exact order and metric geometry:

- convex-order and centered-interval peakedness chains;
- an exact first absolute moment formula;
- a fixed, stage-independent density single crossing;
- exact `W_1`, Kolmogorov, total-variation, stop-loss, order-two Zolotarev, and `W_∞` errors;
- an exact Thue–Morse call/put spline and all-orders stop-loss expansion;
- a simultaneous no-go theorem for acceleration by positive mixtures;
- entropy monotonicity, forward/reverse KL asymmetry, and the finite-stage Fisher-information criterion.

Entropy/KL/Fisher and fixed finite-order Wasserstein coefficient expansions are explicitly labeled conjectural because their formal derivations require endpoint-weighted remainder bounds beyond ordinary `C^r` convergence.
