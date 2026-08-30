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

## Main layer not found in the audited TeX corpus

Targeted tree/search checks found no report-level treatment of the following
combination:

- log-concavity of the up-law and the resulting Fabius Turán inequality;
- native Szegő/Nevai/Rakhmanov asymptotics;
- Christoffel reconstruction of `up` from rational moment matrices;
- the central rational limit `N lambda_N(0) -> pi`;
- the alternating Jacobi product
  `pi = 2 product beta_(2j)/beta_(2j-1)`;
- its exact harmonic-mean relation to central Christoffel approximants;
- the Gauss/J-fraction/Padé package for the native Cauchy transform;
- the finite Legendre--Gaunt determinant formula recovering native Jacobi
  coefficients and closing the spectral reconstruction circuit.

The recent Legendre reports solve a different problem: they expand the bump in
classical Legendre polynomials and synthesize those polynomials from shifted
copies of the bump.  The new report instead orthogonalizes against the measure
`up(x) dx` itself and then connects that intrinsic system back to Legendre data
through finite Gaunt matrices.

## Status discipline

The report marks each statement as one of:

- repository baseline;
- new elementary proof/identity;
- classical external theorem with Fabius-specific hypotheses checked;
- numerical observation, validated through degree 200 at 4,800 decimal digits;
- conjecture or proposed research direction.

The phrase “new result” is corpus-relative and does not assert worldwide
priority.
