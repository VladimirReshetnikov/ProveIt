# Integration ledger: Harmonic Gaps, Gamma Derivatives, and Mixed Tail Moments

## Source and status

This package is a proposed analytic contribution for review and integration into ProveIt. No repository file was modified, merged, or published by preparing it. The ordinary mathematical proofs are in the article. Exact finite verification and numerical diagnostics are documented separately; neither constitutes proof-assistant formalization or external peer review.

Frozen source revision: `7bd45777a8a127e5dc69aff8887ca36a79a3059d`.

Source roots:

- `Analysis/Polylogarithms/docs/manuscript`
- `docs/incoming`

The immutable source inventories and hashes are recorded in `provenance/incoming_archive_manifest.json` and `provenance/manuscript_manifest.json`. The first covers the incoming archives and directory README; the second records all 90 manuscript blobs at the pinned revision.

The immediate source questions are R1, R7, and R8 in `sections/07_research.tex` of `ProveIt_Harmonic_Parity_and_Resolvent_Identities_2026-10-11.zip`. Its `sections/04_harmonic_reduction.tex` supplies the relative harmonic normalization, fixed nonpositive-index deletion, canonical gap polynomials, and one-free-order zero-block generator.

## Question-to-result map

| Source question | Proposed status update | Main article locations | Precise remaining boundary |
|---|---|---|---|
| R1: mixed even-tail centered moments, starting with orders two and four | **Answered for every pair of even-order tails and every centered even moment.** This settles the full two-factor sector, rather than the larger family with arbitrary additional harmonic factors. | Section 4; `mt:regularity`, `mt:all-moments`, `mt:closure`, `mt:generator` | Extra harmonic factors, four or more tails, ordinary-zeta reductions of first spectral derivatives, and arithmetic minimality of the displayed span remain open. |
| R7: a jointly convergent all-zero-block generator with several free orders | **Answered for arbitrary depth and arbitrary independent complex free orders.** The full decoration domain is `|u_j|<1`, independently of depth, and all fixed mixed spectral derivatives converge locally normally. | Section 2; `zbg:bounds`, `zbg:entire`, `zbg:main` | No minimality theorem for an unspecified class of generating kernels is asserted. More general nonzero decoration families and global boundary-monodromy questions are separate problems. |
| R8: transverse derivative at an index subsequently deleted at zero or a nonpositive integer | **Answered for one marked index, every derivative order, and every nonpositive marked center.** The first case is an explicit log-Gamma gap; arbitrary unmarked nonpositive decorations have a finite stated gap-function list. | Section 3; `tr:jointD`, `tr:gap`, `tr:integral`, `tr:negativeD`, `tr:finitefamily` | Several independently marked indices are not proved to close in the same one-marked family. General arithmetic reduction of the retained decorated ordered sums is not claimed. |

The all-zero-block result can also be differentiated in one marked free slot before specialization, giving a convergent version of the one-marked transverse theorem on the same unit polydisc.

## Placement recommendations

The package is coherent as a self-contained continuation after the incoming harmonic-parity report. If its results are subsequently incorporated into canonical chapters:

1. Place the joint generator after the existing entire relative Hurwitz character and canonical nonpositive-index gap reduction. Preserve its source attribution and its definition on the consecutive-sum twist tube.
2. Place the transverse section immediately after fixed-index deletion, since it explains precisely what extra information differentiation introduces. Retain the completed function `Q(u,x)=ζ(u,x)-1/(u-1)` and the initial convergence domains of the weighted paired sums.
3. Place the mixed-tail section with centered harmonic Dirichlet series or exact polygamma moments. Preserve both the ordinary bracketed-sum form and its continuation theorem; these are equivalent only after the stated subtraction proof.
4. Preserve Section 5's boundary counterexample alongside the continued weighted-tail identities. It prevents an apparently innocuous substitution from changing their values.

All principal labels are namespaced by `zbg:`, `tr:`, `mt:`, `audit:`, or `scope:`. The article's independent source files can be integrated individually after their hypotheses and references are made available.

## Attribution to retain

- **Ihara, Nakamura, and Yamamoto:** the underlying geometric Mellin kernel, the original entire interpolation of truncated multiple zeta functions, and the established harmonic product structure. The divided-difference organization in this report is a useful presentation of that existing kernel. Cite the published paper in *The Ramanujan Journal* 67 (2025), article 1, DOI `10.1007/s11139-025-01045-2`, with arXiv:2407.20509 retained as an accessible precursor.
- **Incoming Independent Orders:** identification of that interpolant and the relative endpoint normalization used here.
- **Incoming Harmonic Parity:** arbitrary-position fixed nonpositive-index deletion, canonical gap-polynomial reduction, and the preceding one-free-order Lerch generator; the centered parity mechanism and trigamma-square baseline.
- **Classical inputs:** Bernoulli/Faulhaber summation, Hurwitz special values and asymptotics, Gamma and Barnes normalizations, and Euler's odd-weight double-zeta reduction. Bradley's 2007 paper supplies a primary elementary proof of the last ingredient.

Advancement is claimed relative to the inspected repository corpus. The package does not claim literature-wide priority for every specialization.

## Normalizations and hypotheses that affect the formulas

### Continued paired tails

The weighted difference means continuation from its stated initial domain, where the separate one-sided series converge. It must not be redefined by literal summation at an isolated improved boundary point.

For `ell_0,0(x)=1/2-x`, `a=2`, `b=1`, the continued value `D_0,0(s;2,1)` is identically `-1/2`, while the literal paired series at `s=1` converges absolutely to `+1/2`. The partial-sum boundary term proves the difference exactly. This is a normalization safeguard established in the present report; it is not attributed as a false theorem to the inspected source.

### Fixed versus moving indices

A deletion formula proved at `u=-m` can be differentiated in its surviving free indices. A derivative in `u` requires a formula established before specialization. This report provides that formula; it does not retroactively license differentiation of a fixed numerical label in earlier identities.

### Strict Bernoulli endpoints

The strict gap uses `B_(m+1)(y)-B_(m+1)(z+1)`. Preserve both `B_1=-1/2` and `B_1(1)=+1/2`. In particular, the zero-index interior deletion has its final `-H(s,t)` term, and the transverse unshifted-potential formula has the corresponding spectral-derivative term.

### Centered moments

The cutoff is `0≤n<N`, and the asymptotic constant is taken in the variable `N`. Centered polynomial subtractions vanish under continuation because `ζ(0,1/2)=0` and `ζ(-2j,1/2)=0`. The oriented finite summation proof nevertheless has a separate rational boundary correction represented by `ζ(0)=-1/2`; it must be retained.

### Complex parameters and additive constants

Endpoint parameters lie in the right half-plane. The twist domain bounds every consecutive imaginary sum. The polylogarithmic primitive is continued as one anchored expression through zero. Gamma and Barnes logarithms retain their stated branches and normalizations. No unspecified additive constants are introduced.

### Finite spanning count

For fixed even tail orders `(a,b)`, the moment list contains at most `max(a,b)` rational coordinates. This is a proved spanning statement. It neither asserts arithmetic independence nor proves that the displayed list is minimal.

## Verification ledger

| Branch | Finite exact assertions | Numerical comparisons |
|---|---:|---:|
| Geometric kernel and zero-block identities | 590 | 0 |
| Mixed-tail boundary algebra | 400 | 0 |
| Mixed-tail finite summation by parts | 60 | 0 |
| Mixed-tail moment evaluations | 0 | 30 |
| Transverse Gamma/Hurwitz/Barnes identities and boundary control | 0 | 15 |
| Normalized Mellin higher derivatives on two independent test functions | 0 | 24 |
| Exponential generators | 0 | 3 |
| **Total** | **1,050** | **72** |

The generator comparisons each use a Taylor sum formed from 65 exact moment coefficients. Those coefficients are inputs to three numerical comparisons, not an additional collection of independent exact assertions.

Numerical working precision is 65 digits for the transverse examples, 80 digits for the normalized Mellin derivatives, and 95 digits for the moment/generator examples. The 24 Mellin cases compare subtracted logarithmic quadrature with derivatives of known elementary Mellin transforms of two quadratic-polynomial exponential functions, including complex parameters. They test the normalization lemma independently; they are not direct numerical quadrature of the relative harmonic triple integral. All 24 passed a `1e-50` threshold, with maximum observed residual about `3.10e-79`, as recorded in `results/mellin_derivatives.json`.

Recorded residuals are floating-point observations; the package does not contain interval certificates for these numerical results. The analytic proofs establish normal convergence, complete branch cancellation, and the unrestricted parameter identities.

## Source audit status and broader open problems

No newly confirmed false source theorem was established in this targeted audit. Bibliographic updating, overlapping incoming result ledgers, and the stated normalization safeguards are the proposed integration corrections.

The Gaussian S6 and revised S8 candidates remain open and unchanged. Existing separators concern specified formal relation spaces and do not establish period nonvanishing. No functional bridge or exact period certificate for those candidates is supplied by this package.

Natural follow-ups include products of more harmonic tails, cancellation of first global spectral-derivative remainders, several independently marked harmonic indices, rationally shifted/colored tails with conductor terms, and exact reductions of the retained ordered gap coordinates.
