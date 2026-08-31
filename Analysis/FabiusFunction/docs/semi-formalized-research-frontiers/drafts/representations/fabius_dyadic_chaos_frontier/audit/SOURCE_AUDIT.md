# Source and literature audit

## Purpose

This file records the controlling repository sources, external mathematical
inputs, and the boundary between imported facts and deductions proved in
`fabius_dyadic_chaos_frontiers.tex`.

## Repository sources

### Current controlling interfaces

1. **Documentation tree**
   `https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs`

   Used to establish the live directory structure and locate the primary,
   glossary, paper, archive, and frontier families.

2. **Primary Fabius--Rvachev exposition**
   `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`

   Used for the Fabius/Rvachev normalization dictionary, random-series model,
   MGF and Fourier products, moments/cumulants, exact dyadic arithmetic,
   Legendre formulas, and endpoint/inverse interfaces.

3. **Semi-formalized frontier synthesis**
   `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/`

   Used as the controlling frontier union after the August 2026 consolidation.
   The thematic volumes were screened for q-series, spectra, arithmetic,
   inverse functions, sampling, integration, representations, and open
   problems.

4. **Recursive path ledger**
   `audit/corpus_manifest_2026-08-27.txt`

   This preserved checkpoint records 78 visible TeX paths and retains names of
   historical or generated sources that are difficult to reconstruct from a
   later consolidated tree.

### Prior packages used as negative controls

The user's file library contained recent reports on information geometry,
Stein--Koopman calculus, common-digit zonoids, Pascal spectral probability,
free/Boolean cumulants, convolution divisors, dyadic Radon profiles,
cyclotomic q limits, and several interpolation/inverse programs. Those reports
were searched because their vocabulary overlaps probability, operators,
Legendre expansions, or q-products. Their established results are not repeated
as new in the present manuscript.

## External mathematical sources and their roles

The report relies only on standard or explicitly cited external results.

- **W. Hoeffding (1948), "A class of statistics with asymptotically normal
  distribution."** Source for the orthogonal decomposition now called the
  Hoeffding or functional-ANOVA decomposition. The infinite-product passage and
  all Fabius-specific component formulas are proved in the report.
- **I. M. Sobol (1993), "Sensitivity estimates for nonlinear mathematical
  models."** Background for variance-based sensitivity indices. The exact
  digitwise indices are deductions from the new component norms.
- **D. Xiu and G. E. Karniadakis (2002), "The Wiener--Askey polynomial chaos for
  stochastic differential equations."** Background for tensor polynomial
  chaos with orthogonal marginal systems.
- **NIST DLMF, spherical Bessel functions and Legendre expansions.** Used for
  the standard integral connecting `exp(xv)` with modified spherical Bessel
  coefficients. The marked active-degree probability law is derived in the
  report.
- **P. Flajolet, X. Gourdon, and P. Dumas (1995), "Mellin transforms and
  asymptotics: harmonic sums."** General Mellin-harmonic-sum methodology. The
  specific transform, residues, periodic coefficients, and remainder estimate
  for the activation mean are worked out explicitly.
- **R. M. Corless et al. (1996), "On the Lambert W function."** Branch and
  asymptotic background for the adaptive degree inversion.
- **J. Arias de Reyna (1982/2017; 2018) and V. A. Rvachev (1990).** Classical
  sources for the compactly supported smooth function and arithmetic Fabius
  theory, mediated by the current ProveIt exposition.
- **J.-P. Allouche and J. Shallit (2003).** Standard automatic-sequence and
  Thue--Morse background.
- **G. Szego, Orthogonal Polynomials.** Standard Legendre normalization and
  asymptotic background.

## Imported interfaces versus new proofs

| Interface | Status in this report |
|---|---|
| Fabius/Rvachev random series and density/CDF bridge | Imported from the repository |
| Infinite hyperbolic-sinc MGF product and dyadic refinement | Imported, normalization checked |
| Bernoulli cumulants and Bell moments | Imported as exact inputs |
| Classical Hoeffding orthogonality theorem | Imported standard theorem |
| Exact exponential component formula | Proved here |
| Product-Bernoulli energy law and Sobol formulas | Proved here |
| Modified spherical-Bessel/Legendre integral | Imported standard identity |
| Marked tensor-Legendre probability law | Proved here |
| Smooth mixed-difference estimate | Proved here |
| Dyadic q-Pochhammer order bound | Proved here |
| Monomial top-energy equality and finite component formulas | Proved here |
| q-binomial leading law and first correction | Proved here |
| Mellin transform of the activation profile | Proved here |
| Log-periodic effective-dimension asymptotic | Proved here |
| Total-variation phase limit | Proved here by explicit coupling |
| Fabius negative-Laplace endpoint product | Imported repository interface |
| No-active atom transfer to that product | Proved here |
| Thue--Morse mixed-difference corner | Proved here |
| Lambert-W inversion principle | Imported standard method |
| Explicit chaos-degree cutoff | Proved here |

## Search vocabulary and exclusions

The novelty screen used exact and semantic searches for combinations of
Fabius/Rvachev/up-function with:

`Hoeffding`, `functional ANOVA`, `Sobol`, `Efron-Stein`, `polynomial chaos`,
`tensor Legendre`, `active digit`, `interaction order`, `effective dimension`,
`Esscher`, `chi-square divergence`, `Poisson-binomial`, `x coth x - 1`,
`1 - tanh x/x`, `phase law`, `Mellin active count`, `best N-term`, and
`downward-closed`.

The audit found neighboring but nonidentical constructions and excluded them
from the novelty ledger:

- martingale decompositions for the doubling map in Fourier-decay reports;
- scalar information-channel identities for prefixes of the geometric random
  series;
- Poisson-binomial laws built from the zero divisor of Pascal--Rvachev
  determinants;
- ordinary one-dimensional Legendre expansions of the Rvachev density;
- generic q-binomial and q-Pochhammer identities;
- existing Lambert-W endpoint and inverse asymptotics.

None supplies the coordinate ANOVA decomposition, its exact active-set energy
measure, or the two-sided phase law of interaction order.

## Numerical and symbolic validation

`experiments.py` is deterministic and network-free. It independently checks:

- the Mellin Fourier coefficients against direct lattice evaluation;
- the no-active identity from two independent products;
- local Legendre Parseval through degree 64;
- q-binomial leading and first-correction formulas;
- the quantitative total-variation phase bound;
- exact rational monomial top energies.

Every infinite sum/product uses a documented truncation or geometric tail
bound. The computed data support transcription and asymptotic checks only; the
proofs remain the mathematical boundary.

## Priority caution

The web and repository searches were targeted, not an exhaustive worldwide
priority investigation. The report therefore uses "repository-new" or
"apparently new relative to the audited corpus" rather than asserting universal
first publication.
