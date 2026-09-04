# Corpus audit and nonduplication boundary

## Target and date

The requested target was the recursive LaTeX documentation tree

`https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs`

including its subdirectories. The public tree, current controlling LaTeX
syntheses, and their manifests were reviewed on 2026-08-30. A preserved
recursive path ledger from 2026-08-27 is included as
`corpus_manifest_2026-08-27.txt` so that paths later absorbed, renamed, or
archived remain visible to the audit.

## Operational coverage convention

This is a living research repository. It contains primary expositions,
consolidated frontier volumes, generated TeX fragments, imported paper
transcriptions, and frozen historical revisions. Counting every path as an
independent mathematical source would overcount repeated claims. The audit
therefore used the following hierarchy:

1. the live primary Fabius--Rvachev exposition for normalizations and proved
   baseline results;
2. the live semi-formalized frontier synthesis and its thematic consolidations
   as the controlling frontier interface;
3. the recursive 78-path checkpoint for negative controls and provenance;
4. targeted full-text searches in relevant historical, draft, paper, and prior
   generated-report sources;
5. close reading of theorem ledgers, open-problem registers, appendices, and
   source audits where a phrase search could miss equivalent mathematics.

Generated tables and byte-identical archived copies were read with their parent
reports but were not counted as independent mathematical contributions.
Consequently, the phrase "all TeX documents" is interpreted claim-wise rather
than as a raw path count.

## Mathematical source families screened

The following families were examined for possible overlap.

- **Primary exposition and glossary:** the bounded Fabius function, the centered
  Rvachev law, the signed global extension, functional-differential equations,
  probability models, Fourier products, moments, cumulants, exact values,
  inverse notation, and normalization conventions.
- **Thue--Morse and digital theory:** Prouhet cancellation, finite products,
  Mahler equations, automatic sequences, valuation formulas, rarefied sums,
  derivative signs, and finite Thue--Morse splines.
- **Exponent and q-series frontiers:** q-Pochhammer and Gaussian-binomial
  identities, geometric interpolation, inverse q-functions, cyclotomic limits,
  natural boundaries, finite sinc products, and reciprocal-q constructions.
- **Spectra and arithmetic:** integer-zero multiplicities, canonical products,
  spectral zeta functions, arithmetic rays, heat and determinant models,
  Pascal--Rvachev hierarchies, and Fourier envelopes.
- **Inverse and endpoint theory:** Lambert-W coordinates, all-order Bell
  expansions, quantile transforms, inverse dyadic values, elasticity, and
  logarithmic-periodic endpoint phases.
- **Integration, sampling, and transforms:** Fourier/Laplace/Mellin/Cauchy
  transforms, fractional calculus, self-sampling, dyadic-comb quadrature,
  Euler--Maclaurin formulas, and Appell deconvolution.
- **Representations and operators:** Legendre/Jacobi/Chebyshev expansions,
  Lagrange/Newton interpolation, shifted-up synthesis, Fredholm and Brownian
  models, zonoids, Stein--Koopman calculus, and multiresolution constructions.
- **Archived papers and historical sources:** classical Fabius/Rvachev papers,
  Arias de Reyna, Haugland, automatic-sequence sources, and imported corrected
  TeX transcriptions.
- **Prior frontier packages in the user's library:** information geometry,
  common-digit zonoids, spectral probability duals, free/Boolean cumulants,
  dyadic Radon profiles, convolution divisors, and other nearby probability or
  operator constructions.

## Established material explicitly excluded from novelty claims

The manuscript imports, rather than relabels as new:

- the random-series model
  `X = sum_{j>=1} 2^{-j} V_j`, with independent `V_j ~ Uniform[-1,1]`;
- the Rvachev density, Fabius CDF, and their affine bridge;
- the moment generating product
  `M(t) = product_j sinh(t/2^j)/(t/2^j)` and its dyadic refinement;
- Bernoulli cumulants, Bell-polynomial moments, and rational moment arithmetic;
- the infinite sinc product, integer zero multiplicities, Fourier decay, and
  Thue--Morse/Prouhet identities;
- exact dyadic Fabius values and q-binomial formulas;
- existing Legendre expansions and polynomial synthesis;
- existing endpoint and inverse-Fabius Lambert-W asymptotics;
- existing information-theoretic, Stein--Koopman, Pascal spectral, zonoid,
  free/Boolean, and Radon-profile results in earlier packages.

## Targeted novelty searches

The controlling repository sources and prior report library were searched for
exact and close variants of the following terms and formulas:

- `Hoeffding decomposition`, `functional ANOVA`, `ANOVA component`,
  `Efron--Stein`, `Sobol index`, and `total Sobol index` in the Fabius/Rvachev
  setting;
- `polynomial chaos`, `tensor Legendre chaos`, `marked Legendre degree`, and
  `local Parseval` for the dyadic uniform digits;
- `active digit`, `active set`, `interaction order`, `effective dimension`,
  `best N-term chaos`, and `downward-closed chaos`;
- `Esscher tilt`, `chi-square divergence`, `no-active atom`, and
  `Poisson-binomial variance law` for the exponential Fabius observable;
- the formulas `x coth(x)-1` and `1-tanh(x)/x` as dyadic activation odds and
  probabilities;
- a q-Pochhammer bound for order-k Hoeffding energies;
- a phase limit for a Bernoulli sum centered by `floor(log_2 t)`;
- Mellin analysis of the effective interaction count, including a periodic
  phase and Fourier coefficients;
- a Thue--Morse interpretation of mixed symmetric differences of the nonlinear
  observable;
- Lambert-W cutoffs for tensor-Legendre degree truncation.

No repository treatment of the theorem network developed in the report was
found. There are close neighbors that were deliberately excluded: martingale
methods for Fourier decay, scalar information channels, spectral
Poisson-binomial laws attached to zero divisors, classical Legendre expansions,
and general q-series identities. None gives the coordinate-wise Hoeffding law,
its exact variance measure, or the phase-limit construction proved here.

## Corpus-relative contributions proved in the report

Relative to the audited corpus, the manuscript develops the following new
layer.

1. **Exact exponential Hoeffding components.** For every finite active set
   `S`, the component of `exp(tX)` factors coordinatewise, with exact squared
   norm
   `M(t)^2 product_{j in S} (x_j coth(x_j)-1)`.
2. **Independent active-set law.** Normalized component energies form a product
   Bernoulli law with
   `p_j(t)=1-tanh(t/2^j)/(t/2^j)`; conditioning on a nonempty active set gives
   the complete variance-share distribution and all Sobol indices.
3. **No-active/chi-square identities.** The empty-set atom is expressed both
   through the MGF ratio and through the negative Fabius Laplace product,
   producing an independently testable exact identity.
4. **Tensor-Legendre refinement.** Each active coordinate carries an exact
   spherical-Bessel degree mark. Local Parseval identities refine the active
   set into a marked polynomial-chaos law.
5. **General smooth-observable bound.** Every order-k interaction is bounded by
   a mixed-derivative estimate; summing over dyadic subsets gives the exact
   q-Pochhammer factor
   `4^{-k(k+1)/2}/(1/4;1/4)_k`.
6. **Sharp polynomial top interactions.** Monomials attain the top-order bound
   exactly, and all lower components admit finite Bell--Bernoulli formulas.
7. **Chaos generating products.** A two-variable product encodes every
   interaction order and satisfies a dyadic refinement identity; Newton and
   Bell transforms give exact order cumulants.
8. **Small-field q-binomial law.** The order energies have a leading Gaussian
   q-binomial profile with a proved first correction and a geometric-q
   extension.
9. **Mellin effective-dimension theorem.** The mean active count has an explicit
   Mellin transform and an asymptotic
   `log_2 t + periodic phase + O(1/t)` with computable Fourier coefficients.
10. **Phase-limit law.** Along `t=2^{n+theta}`, the centered interaction order
    converges in total variation to an explicit two-sided Bernoulli-defect law,
    with a quantitative coupling bound and a conditioned variance-share
    version.
11. **Thue--Morse nonlinear corner.** Every finite mixed symmetric difference
    is an exact Thue--Morse signed sum; for the exponential observable it
    reproduces the Hoeffding factorization.
12. **Lambert-W degree cutoff.** Uniform asymptotics for local Legendre marks
    yield a Lambert-W formula for adaptive tensor-degree truncation.

The report also isolates conjectures on phase-mode uniqueness, differential
transcendence, strict log-concavity, the full geometric-q phase diagram,
inverse-Fabius chaos, automatic signs, and optimal nonlinear approximation.

## Priority convention

"New" means *not located in the audited repository state or in the prior
packages used as negative controls*. It is not an unconditional claim of
worldwide historical priority. Hoeffding decompositions, Sobol indices,
polynomial chaos, Mellin harmonic-sum analysis, spherical Bessel functions,
q-binomial identities, and Lambert W are classical ingredients. The claimed
novelty is their exact composition with the dyadic Fabius--Rvachev product and
the resulting theorem network.

## Reproducibility boundary

The archive contains the full source, rendered PDF, commented deterministic
Python program, generated CSV tables, vector/raster figures, numerical summary,
source audit, preserved recursive path ledger, dependency file, and build
guide. Historical integrity receipts remain recoverable from Git history.
Numerical work checks identities and asymptotic
predictions; it is not used in place of proofs.
