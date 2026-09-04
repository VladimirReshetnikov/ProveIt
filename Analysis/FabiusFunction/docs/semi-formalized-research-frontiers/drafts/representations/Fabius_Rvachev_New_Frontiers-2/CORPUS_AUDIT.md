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
The current repository has since added seven executable-rational modules beside
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
- `FabiusLegendreRationalGramValues.lean` contributes no definitions and exactly
  eleven public theorems: `moment_four`,
  `rvachevLegendreGramDetRat_one`, `rvachevLegendreGramDetRat_two`,
  `rvachevLegendreGramDetRat_three`, `rvachevLegendreGramDetRat_four`,
  `rvachevLegendreGramDetRat_five`, `rvachevOrthoNormRat_four`,
  `rvachevJacobiSubdiagonalRat_three`, `hankelRatio_four`,
  `integral_sq_upOrthoPolynomial_four`, and
  `hankelRatio_four_div_three`.  They compute the raw eighth moment
  `132809/32531625`; rational Legendre Gram determinants of orders one through
  five `1`, `1/9`, `8/2025`, `39616/602791875`, and
  `16544275456/27453718922765625`; the report norm
  `H_4 = 26727424/55791736875`; and, at zero-based subdiagonal index three, the
  conventional `beta_4 = 835232/4640643`.  The first eight rational computations
  are unconditional.  The real Hankel-ratio value, squared-integral value, and
  fourth/third Hankel-ratio quotient each require a `BoundedFabius` input and an
  `IsFabius` certificate.
- `LegendreGaunt.lean` contributes exactly four public definitions,
  `legendreLebesgueMomentRat`, `legendreGauntRat`, `legendreGaunt`, and
  `legendreProductLinearizationCoeffRat`, and twelve public theorems:
  `legendreLebesgueMomentRat_even`, `legendreLebesgueMomentRat_odd`,
  `legendreLebesgueMomentRat_cast`, `legendreGauntRat_eq_momentFunctional`,
  `legendreGauntRat_cast`, `legendreGauntRat_swap_left`,
  `legendreGauntRat_swap_right`, `legendrePolynomial_mul_eq_sum_gaunt`,
  `legendrePolynomialRat_mul_eq_sum_gaunt`,
  `legendreGauntRat_eq_zero_of_odd_sum`,
  `legendreGauntRat_eq_zero_of_add_lt`, and
  `legendreGauntRat_eq_zero_of_triangle_violation`.  The executable rational
  monomial moments feed a bounded triple coefficient sum whose cast is the real
  triple-Legendre interval integral.  The module proves the swap symmetries,
  exact finite product linearization over `ℚ` and `ℝ`, and necessary
  odd-sum and strict-triangle vanishing conditions.  It proves no converse or
  nonvanishing result, Wigner `3j` identification, factorial formula, or
  nonnegativity derived from Wigner symbols.
- `FabiusLegendreGaunt.lean` contributes exactly one public definition,
  `canonicalRvachevFullLegendreCoefficientRat`, and eight public theorems:
  `canonicalRvachevFullLegendreCoefficientRat_even`,
  `canonicalRvachevFullLegendreCoefficientRat_odd`,
  `canonicalRvachevFullLegendreCoefficientRat_cast`,
  `canonicalRvachevFullLegendreCoefficientRat_eq_normalized_moment`,
  `rvachevLegendreGramEntryRat_eq_sum_full_gaunt`,
  `rvachevLegendreGramEntryRat_eq_sum_gaunt`,
  `rvachevLegendreGramMatrixRat_apply_eq_sum_gaunt`, and
  `upLegendreGramMatrix_apply_eq_sum_gaunt`.  The full/even rational coefficient,
  normalized-moment, Gram-entry, and matrix identities are unconditional.  The
  coefficient cast and real up-Gram finite even sum require `BoundedFabius` and
  `IsFabius`.  These are finite polynomial and finite-sum identities, not an
  infinite-series/integral interchange.
- `LegendreGauntClosedForm.lean` contributes exactly two public definitions and
  twenty-five public theorems.  `legendreGauntAdmissible` is the even
  weak-triangle support and `legendreWignerThreeJZeroSqRat` is the total
  rational integer-index zero-row square datum.  The theorems prove the
  pairwise-add central-binomial and factorial forms, the half-sum factorial
  form, the boundary and zero-index cases, the unconditional rational and real
  identities `Gaunt = 2 * square`, sharp support, zero, positivity and
  nonnegativity, and the product-linearization coefficient bridge.  The
  square notation makes no signed-symbol or phase choice and supplies no
  half-integer, nonzero-magnetic-index, general `3j`/`6j`/`9j`, orthogonality,
  or recoupling API.
- `FabiusLegendreGauntClosedForm.lean` contributes zero definitions and three
  public theorems:
  `rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat`,
  `rvachevLegendreGramMatrixRat_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`,
  and `upLegendreGramMatrix_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`.
  They give the finite rational entry, rational matrix-entry, and real up-law
  matrix-entry Wigner-square sums; the real bridge retains its
  `BoundedFabius` and `IsFabius` hypotheses.

Thus executable rational coefficient, entry, matrix, determinant, cast,
positivity, norm-ratio, and Jacobi-ratio layers now have exact Lean
counterparts, and the displayed `H_4` and `beta_4` now have named exact values.
The rational Gaunt triple sum, its real integral cast, rational/real product
linearizations, rational/real finite Rvachev Gram-entry expansions, total
integer-index zero-row square datum, factorial form, sharp support and
positivity, nonnegativity, and finite Wigner-square matrix now have exact Lean
counterparts.
A signed symbol, phase convention, half-integer and nonzero-magnetic-index
objects, general Wigner orthogonality/recoupling, Christoffel reconstruction,
named `G_3` entry values, roots, quadrature, infinite Jacobi products, and
asymptotics remain paper-only.  The report keeps the original 22-declaration
coefficient/Gram inventory, the exhaustive eleven-theorem values inventory,
the 25-declaration Gaunt inventory, and the 30-declaration closed-form/wrapper
addition separate.  The two closed-form leaves add thirty names, so the focused
report crosswalk grows from 76 to 106 names; the broader eleven-module
inventory has twenty definitions and 109 theorems, 129 declarations in all.
The retained 41-page PDF is a verified historical 99-name artifact and
predates this last addition.

The previously validated PDF and preflight receipt predate this crosswalk
correction. They remain historical evidence but are stale for the current
source; a new build and refreshed preflight are pending.

## Status discipline

The report marks each statement as one of:

- repository baseline;
- new elementary proof/identity;
- classical external theorem with Fabius-specific hypotheses checked;
- numerical observation, validated through degree 200 at 4,800 decimal digits;
- conjecture or proposed research direction.

The phrase “new result” is corpus-relative and does not assert worldwide
priority.
