# Verification record

The article's proofs establish the all-order statements. The following finite
checks were run successfully from the packaged source tree. All exact checks
use rational or symbolic arithmetic; numerical calculations are separately
identified as diagnostics.

## Exact replay

| Script | Checked scope | Result |
|---|---|---|
| `verify_gap_four.py` | 10 source/operator matrix conjugacies; 16 determinant formulas; 44 formal null-series coefficients; 21 ratio comparisons; 22 Bernoulli comparisons; 210 normalized-weight comparisons | 323 exact checks passed |
| `verify_complementary.py` | Every `1 <= a < b <= 10` boundary determinant, plus 140 increasing-row ratio minors at `m=2,3,4,5` | 185 exact checks passed |
| `verify_telescoping.py` | Nine even-order examples, including the complete `(8,12)` extraction; source-coordinate agreement; finite rational difference identity in independent tail variables; zero initial value; cancellation of every positive endpoint power; limiting constant | All nine certificate cases passed |
| `verify_gamma_sectors.py` | Complete `A_m = N(A_m) + D H(A_m)` identities through weight 24; all 575 possible three-variable coefficients in that range; nine numerator-polynomial identities through sector 10; 40 closed-function coefficients; two endpoint checks | 651 exact checks passed |
| `verify_higher_resonance.py` | 16 finite cutoff identities, 29 generating-function coefficients, and three symbolic identities | 48 exact checks passed |
| `verify_logarithmic_spectral.py` | Universal spatial kernel coefficients through order 10 | 10 exact checks passed |

This is 1,217 enumerated exact checks plus nine full telescoping certificate
cases. The count describes the replay, not the strength or generality of a proof.
For example, finite positivity checks are not used to infer positivity at all
indices: the ratio lemma proves it by induction.

## Independent numerical diagnostics

The logarithmic spectral script used 70-digit working precision. It compared
ordinary subtracted integrals against the spectral formulas for digamma-square
and trigamma-square polynomials at orders 1 through 4. The largest absolute
residual was approximately `7.8e-68`. Two complex-parameter evaluations of the
normalized Mellin identity had residuals below `9.4e-57`. Local Taylor series and
small-argument asymptotic expansions were used to avoid subtractive loss in
the quadrature. These are floating-point diagnostics, not interval certificates.

The resonance script used 65-digit working precision. Independent Euler-kernel
integrals for the first two convergent primitive endpoints agreed with their
zeta evaluations to residuals approximately `2.4e-66` and `-5.8e-66`. It also
checked real and complex parameter cutoffs, the spectral Laurent expansion,
and the uniform deformation at positive, negative, complex, and near-zero
values of the parameter.

The generalized Stieltjes checks used a finite sum through 20,000 and a leading
asymptotic tail correction. Their residuals were approximately `-1.44e-8` and
`1.29e-7` for derivative orders 0 and 1. Those finite-tail diagnostics should
not be reported as 65-digit confirmations. Similarly, the finite-cutoff checks
verify convergence of the displayed asymptotic model and retain its nonzero
remainder; they are not exact evaluations of the cutoff by the asymptotic terms.

## Exact data representation

`gamma_normal_forms.json` represents a monomial by its sorted list of derivative
indices. Thus `[0,0,2,2]` means `u_0^2 u_2^2`. Coefficients are rational strings.
For each weight it supplies the complete normal polynomial and its primitive,
through weight 14. The checked range through weight 24 is larger than the
printed-table range.

`gamma_sector_numerators.json` supplies the exact polynomials `p_b(X)` and the
associated rational functions `r_b(X)` through `b=10`.
`gamma_endpoints.json` retains gamma and the ordinary zeta values as formal
symbols, without applying optional even-zeta reductions.
`extract_812.json` and `telescoping_results.json` contain the matrix/inverse-row
data and the independently derived finite certificate, respectively.

## Source provenance and audit

The Git commit is fixed at
`446dca9bd65c20e409d1d2561d4ffad408103e2a`.
`download_manifest.json` gives repository paths, Git blob identifiers, and sizes;
`download_results.json` gives the downloaded sizes and SHA-256 hashes.
The six ZIP hashes identify the exact incoming report contents.
`source_title_metadata.json` preserves their literal titles, dates, and source
baselines. The reports' own earlier baselines are distinguished from the newer
commit at which this audit inspected them.

The mathematical audit was targeted at the proof chains used in this article.
It does not certify every result elsewhere in the repository. No new false
inherited theorem was established. The source-status changes are explicitly
classified in the article and in `integration/claims.json`.

## Typesetting

The complete PDF was compiled with resolved citations and cross-references.
The final build has no LaTeX overfull-box or underfull-box warnings. Every page
was rendered for layout review, with full-size inspection of the dense theorem,
integral, coefficient, and status-table pages. The single-file TeX version was
also compiled independently and checked against the modular version.
