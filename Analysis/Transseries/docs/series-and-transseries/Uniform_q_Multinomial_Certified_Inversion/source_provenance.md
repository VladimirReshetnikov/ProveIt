# Source provenance and claim boundaries

Inspected on 29 September 2026. Repository access was through the connected GitHub read/search tools. The repository was not modified.

## Snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

The initial repository snapshot was identified as the following commit (also confirmed as the parent commit in a subsequent branch-metadata read):

    04e06e032dff1966513bfba316966d52db3646b4

The claim of resolving an explicitly recorded gap is relative to the inspected source/version, not to future repository changes.

## Principal companion source

Path:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex

Content blob SHA:

    77e494fbd30587b61b36f0e0e010c85cae3c7fa7

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/04e06e032dff1966513bfba316966d52db3646b4/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex

Directly relevant read ranges included 4080–4140 and 4120–4380. A final pinned read of lines 4180–4240 at the stated commit reconfirmed both the gap and the companion content blob SHA. A preceding range beginning at 3800 supplied the generalized Galois/root-lattice-theta context for one proposed research direction. These reads were not an exhaustive line-by-line audit of the full companion or the larger canonical transseries volume.

Key inspected labels:

- `t3:prop:double-A`: finite-order uniform tail expansion only for tau>=tau_0>0.
- `t3:eq:double-Aexact`: exact Bose-series tail.
- `t3:eq:double-A`: Bernoulli–polylogarithm expansion.
- `t3:eq:modularP`: exact modular Euler-product identity.
- `t3:eq:modularsectors`: convergent modular exponential sectors.
- `t3:eq:Sphase`: central Gaussian dilogarithmic phase.
- `t3:eq:Slarge`: followed by the explicit statement that uniform matching all the way to tau=0 requires a different error analysis.
- `t3:eq:crossover-all`: pre-existing formal all-order inverse coefficients.

The present paper does not claim the pre-existing phase, modular identity, or inverse coefficient formula as new. Its extension consists of the all-h signed bounds and normalized coefficients, exact Borel description adapted to the ray, uniform exponential estimate, sharp endpoint/resonant equivalents, and uniform conditioning/enclosures proved in the article.

## Group README

Path:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/README.md

Blob SHA:

    516aaa30e84cb0036a00f803cb6e8e3026febb8e

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/04e06e032dff1966513bfba316966d52db3646b4/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/README.md

Used for the relationship between the canonical and companion volumes, existing residual/error transport and staircase inversion, and qualifications about the formal crosswalk. No new formalization count or successful Lean build is asserted by the present article.

## Primary external sources

- NIST DLMF §4.36, Infinite Products and Partial Fractions: https://dlmf.nist.gov/4.36
  Used for the classical hyperbolic partial-fraction kernel.
- NIST DLMF §23.18, Modular Transformations: https://dlmf.nist.gov/23.18
  Used for the eta modular transformation underlying the Euler-product identity.
- NIST DLMF §5.9, Integral Representations: https://dlmf.nist.gov/5.9
  Used for Binet/digamma/trigamma integral background.
- NIST DLMF §5.11, Asymptotic Expansions: https://dlmf.nist.gov/5.11
  Used for classical gamma/Stirling asymptotic background.
- Ovidiu Costin and Stavros Garoufalidis, *Resurgence of the Euler–MacLaurin summation formula*, arXiv:math/0703641, version 2 (2007): https://arxiv.org/abs/math/0703641
  Establishes relevant prior resurgence machinery; the paper does not claim that framework as new.
- Stavros Garoufalidis and Rinat Kashaev, *Resurgence of Faddeev's quantum dilogarithm*, arXiv:2008.12465 (2020): https://arxiv.org/abs/2008.12465
  Relevant prior explicit Borel-pole and Stokes analysis. The abstract and initial theorem pages were inspected, including PDF page screenshots.

This was a targeted literature search, not an exhaustive priority or originality certification.
