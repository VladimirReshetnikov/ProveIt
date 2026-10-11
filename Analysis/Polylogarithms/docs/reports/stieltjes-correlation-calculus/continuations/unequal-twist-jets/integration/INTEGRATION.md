# Additive integration map

## Proposed destination

Canonical fragment: `07-unequal-twist-jets.tex`.
Proposed location:
`Analysis/Polylogarithms/docs/manuscript/chapters/07-unequal-twist-jets.tex`.
Include it immediately after the existing `07-mixed-twist-identities.tex` on
the Hurwitz/Stieltjes volume's dependency chain. Existing historical chapter
filenames use `07-` even though this material is in the later volume's Chapter
8; preserve the repository's established naming convention.

The fragment is self-contained at the proof level for its selected central,
closure, symmetric, ordinary-Gamma and cutoff statements. Its four-page
`addendum-preview.pdf` and minimal driver were built separately. It introduces
only `utj:` labels and no global macros. It requires standard amsmath, amssymb,
amsthm and the canonical theorem/proof environments.

## Complete report retention

Retain the full article and scripts as a report, for example under
`Analysis/Polylogarithms/docs/reports/unequal-twist-stieltjes-jets/`.
The full report supplies all details, attribution, arbitrary-mode repair,
higher primitives, the complete spectral-ray theorem, cyclotomic formulas,
source audit and future research programme. Do not silently treat a concise
fragment as incorporating every claim of the full report.

## Conventions to preserve

1. The Fourier branch is log(2*pi*abs(n+theta)) plus i*pi/2 times the sign.
   The twisted zero Fourier coefficient is retained.
2. `J_m^(r,theta) = (-1)^m d^m/d(alpha)^m K_alpha^theta at alpha=r`.
   The derivative sign is important.
3. The canonical Stieltjes coefficients have residue `-delta/u` at s=1.
   The symmetric U0 product contains `-zeta(2) delta`.
4. The closure result concerns an explicitly specified integer-order finite
   functional span with frequency-independent coefficients. Do not relabel it
   as arithmetic nonreduction of an individual value.
5. C_(m,n) uses the sharp cutoff log(N)^(m+n+1)/(m+n+1). The spectral-ray
   theorem uses its stated one-variable restriction; these are not generic
   interchangeable finite-part conventions.

## Editorial actions proposed, not applied

Reconcile or date the opening source count in EDITORIAL-LEDGER.md (439 versus
746 in the later overview). Do not assert a fresh recount based on this report.
Add a bibliography entry for the retained report and preserve the attribution
to the classical DLMF identities. A repository-native rebuilt volume still
requires its own cross-reference validation, native replays and rendered review.

No repository commit, pull request, issue or file write was performed.
