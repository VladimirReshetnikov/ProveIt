# Source and claim audit

## Immutable repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `37e61c1fdec28c6e7ab7ff445043993077b42cbd`

Source inspection date: September 28, 2026 (US Pacific date).

The baseline was pinned before development. Some discovery searches operated
on the default branch; mathematical comparisons and citations in the article
use files fetched at the pinned commit. This is a targeted review of the
relevant sampling/comb material, not an exhaustive audit of the repository.

## Primary inspected repository paths

1. `Analysis/FabiusFunction/Lean/FabiusFunction/RvachevSuperconvergentSynthesis.lean`
   The header, definitions, and quadrature statements were inspected.
   They establish the selected phases as sufficient at every positive integer
   mesh, and explicitly do not assert phase completeness.

2. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/chapters/03_additive_dyadic.tex`
   Inspected ranges: 1–100, 1500–1650, 2030–2200, and 2200–2420.
   This prose source already contains the labels `lem:multiple-angle`,
   `thm:phase-zero-set`, and `thm:up-composite-mesh`, as well as the exact
   low-level defect table and the discussion of mixed higher jets.
   In particular, the phase-zero classification is NOT wholly open merely
   because the selected Lean module does not state its converse.

3. The READMEs for the Fabius research frontiers and the canonical comb
   synthesis were inspected to distinguish proof-bearing source, historical
   build claims, formal theorem surfaces, and prose results.

## Inherited mathematical content

- The probability model and dyadic sinc Fourier product for the up-function.
- Integer zero multiplicity 1+v2(n).
- Composite-mesh polynomial exactness at degree v2(M).
- The leading integer-zero jet and first-failure alias series.
- Parity-selected superconvergence and existing phase-zero classifications.
- The one-factor odd-dilation comparison proportional to 1/n.
- The binary/Thue–Morse sign pattern.
- Four exact even-mesh defect values reproduced in the article.

The paper credits these as inherited. Self-contained proofs are included to
fix conventions, not to imply that they were first discovered here.

## Proposed contributions in the package

- Classification of all finite signed phase measures that give uniform
  polynomial exactness at rational and irrational real meshes.
- Minimum support, divisibility of support size, and the equality-case
  assertion that a minimum-support signed rule must be positive and uniform.
- Finite annihilating-polynomial certificates yielding quantitative positive
  error obstructions for every under-budget signed filter, without imposing
  a total-variation bound on its weights.
- The second exactly controlled sinc factor, giving a 1/n^2 comparison.
- The multiscale relative log-Gaussian bound uniform over the odd mesh factor.
- The resulting explicit positive relative factor, simple roots, and global
  distance-to-phase error estimates in a unified integer-mesh statement.

These are candidate research contributions with proofs provided in the
article, not a certification of priority. Related facts may be known under
other formulations; a broader literature review and independent mathematical
review remain appropriate before publication as original research.

## External primary references

- J. Arias de Reyna, “An infinitely differentiable function with compact
  support: Definition and properties,” arXiv:1702.05442 (2017), an English
  translation of the author's 1982 paper.
  https://arxiv.org/abs/1702.05442

- V. G. Zakharov, “Polynomial spaces reproduced by elliptic scaling
  functions,” arXiv:1310.8425 (2013).
  https://arxiv.org/abs/1310.8425

The first supplies classical background. The second situates Fourier-zero
polynomial-reproduction criteria in the Strang–Fix literature. Neither is
cited as a source for the new signed-filter theorem. No third-party papers
or repository source files are redistributed in this package.

## Verification boundaries

The exact script checks finite instances using rational arithmetic. The
optional high-precision part is not an interval proof. General validity rests
on the written proofs, not on numerical sampling. No Lean formalization of
the proposed results is supplied, and no Lean build or axiom audit was run.
The full arbitrary-phase polynomial exactness quantifier must be preserved
when porting the results.
