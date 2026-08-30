# Corpus audit and nonduplication boundary

## Pinned snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Commit: `b863b90ee74ec0405af2d67ad04c61824c3aea00`
- Audit date: 2026-08-30
- Requested scope: `Analysis/FabiusFunction/docs/**/*.tex`

The branch advanced while the research was in progress.  The report was
rebased to and frozen against the commit above.

## Source strata examined

The tree contains several logically different kinds of TeX sources.  The audit
did not count archived or generated siblings as independent evidence.

1. Current proof-backed exposition, especially
   `Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`.
2. The current mathematical glossary and non-elementarity report.
3. Vendored source papers, including the 2017 analytic and arithmetic papers
   by Juan Arias de Reyna.
4. The consolidated semi-formalized frontier volume and its thematic drafts.
5. Recent representation reports, particularly the Legendre/Rvachev and
   Lagrange/Rvachev closed-loop reports.
6. Archived and superseded reports.
7. Generated TeX tables and fragments used as inputs to larger documents.
8. `PAPER_COVERAGE.md`, README files, manifests, and audit documents that map
   prose claims to Lean declarations and identify superseded material.

## Existing results treated as baseline

The report does not claim novelty for the following repository material:

- the bounded Fabius CDF and Rvachev up-function, their support, symmetry,
  differential/refinement laws, smoothness, flat endpoints, and probability
  representations;
- Thue--Morse and infinite-sinc products, finite convolutions, Poisson
  summation, and dyadic arithmetic;
- exact rational moments, Bernoulli cumulants, Bell-polynomial moment formulas,
  positive Hankel matrices, and low-degree native orthogonal polynomials;
- endpoint log-square and Lambert-W inverse asymptotics;
- q-Pochhammer/Gaussian-binomial identities and geometric extrapolation
  filters;
- Fourier--Legendre expansions, shifted-up synthesis of polynomials, and the
  recent Legendre/Lagrange reconstruction loops;
- the Cauchy-transform Laurent expansion and dyadic renormalization identity.

## Distinctive layer after overlap correction

The arrival-time audit overstated the absence of native asymptotic and
transform material. At the pinned checkpoint, the canonical representation
frontier already contained the Nevai-limit, J-fraction, Hankel, and
Gauss--Padé program. Those ingredients are inherited overlap. The filed
report's useful combined layer consists of:

- log-concavity of the up-law and the resulting Fabius Turán inequality;
- a single report connecting native Szegő/Rakhmanov consequences to the
  already-recorded Nevai layer;
- Christoffel reconstruction of `up` from rational moment matrices;
- the central rational limit `N lambda_N(0) -> pi`;
- the alternating Jacobi product
  `pi = 2 product beta_(2j)/beta_(2j-1)`;
- its exact harmonic-mean relation to central Christoffel approximants;
- an expanded Gauss/J-fraction/Padé presentation for the native Cauchy
  transform, overlapping the canonical frontier;
- the finite Legendre--Gaunt determinant formula recovering native Jacobi
coefficients and closing the spectral reconstruction circuit.

Accordingly, this list is a disposition map rather than a claim that every
ingredient was absent. The package remains standalone pending a
claim-by-claim deduplication against the current representation volume.

The recent Legendre reports solve a different problem: they expand the bump in
classical Legendre polynomials and synthesize those polynomials from shifted
copies of the bump.  The new report instead orthogonalizes against the measure
`up(x) dx` itself and then connects that intrinsic system back to Legendre data
through finite Gaunt matrices.

## Post-snapshot Lean crosswalk

The pinned audit and its corpus-relative novelty statements remain historical.
The current repository has since added two executable-rational modules beside
the generic moment-Gram and real Fabius--Legendre determinant layers:

- `LegendrePolynomialRational.lean` contributes two public definitions and six
  public theorems for executable rational Legendre coefficients, their
  polynomial wrapper, exact degree and leading coefficient, nonvanishing and
  consecutive-leading-coefficient quotient, and the real-cast bridge.
- `FabiusLegendreRationalGram.lean` contributes three public definitions and
  eleven public theorems for bounded rational entry sums, their finite matrix
  and determinant, abstract-moment identifications, real-cast bridges,
  determinant identity and positivity, and rational norm/Jacobi determinant
  ratios.  Each of the three real-cast bridges assumes both `BoundedFabius`
  and `IsFabius`; the finite rational identities do not.

Thus executable rational coefficient, entry, matrix, determinant, cast,
positivity, norm-ratio, and Jacobi-ratio layers now have exact Lean
counterparts.  The finite Gaunt/Wigner/3j entry expansion and rationality by
that route remain paper-only, as do Christoffel reconstruction, root results,
quadrature, infinite Jacobi products, and asymptotics.  The report's dedicated
API inventory names all 22 new declarations once; it does not duplicate the
pre-existing generic and real module inventories.

## Status discipline

The report marks each statement as one of:

- repository baseline;
- new elementary proof/identity;
- classical external theorem with Fabius-specific hypotheses checked;
- numerical observation, validated through degree 200 at 4,800 decimal digits;
- conjecture or proposed research direction.

The phrase “new result” is corpus-relative and does not assert worldwide
priority.
