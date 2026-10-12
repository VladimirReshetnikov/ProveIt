# Integration notes

## Proposed location

A natural new report-continuation directory is

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/connected-spectral-gamma/`

This is a suggestion, not a statement that the path already exists. Preserve
the original delivered package according to the repository's incoming-report
procedure. The delivery does not alter or overwrite the repository.

## Mathematical dependency and normalization map

The standalone article is independent of unaccepted incoming theorems. Its
analytic inputs are classical Hurwitz continuation, the residue-one Laurent
expansion at s=1, digamma difference sums, beta integration, and the Cauchy
formula for divided differences. The main proof needs only the expansion

`D_s(x,u) = -u*x^(-1-s) + O(x^(-2-Re(s)))`.

Use the convention

`zeta(1+w,a) = 1/w + sum((-1)^N*gamma_N(a)*w^N/N!)`.

The regular mixed primitive is F_alpha = (-1)^(m+|alpha|) times the corresponding
spectral derivative of H. In particular, the equal-line mth derivative of the
connected spectrum is (-1)^m*m!*F_zero. The mixed shift derivative must be
performed before restricting all shifts to the same value.

Every individual linear factor uses its right-half-plane principal logarithm.
For complex shifts a bracketed spectral product uses the sum of these factor
logarithms, not an assumed identity for the principal logarithm of the product.
The notation log Gamma uses its holomorphic right-half-plane branch, real on the positive axis, not a pointwise principal log of the Gamma value.
The one-dimensional real Gamma integrals are stated for positive real shifts;
the normally convergent definitions cover Re(a+u_j)>0.

## Suggested reading and integration order

Start with article Section 2 (critical germ), Section 3 (ordinary primitives and
Gauss law), and Section 4 (complete collisions). Section 5 converts the unmarked
primitive into one-dimensional Gamma integrals. Sections 6–8 give harmonic,
polylogarithmic, and antiderivative consequences. Section 9 handles polynomial
weights. Section 10 and `SOURCE_AUDIT.md` delimit proof and review status.

`integration/connected_spectral_insert.tex` is a compact fragment using the
parent's standard theorem/proof environments and AMS math commands. Its labels
are prefixed `connected:`. It uses no preamble and does not duplicate the full
article. Read its final normalization note before making any notation changes.
The parent manuscript remains responsible for full analytic proof audit and
consistent cross-references before promoting a theorem into its canonical text.

## Overlap and open problems

The earlier quadratic and higher-defect reports may overlap the m=2 and
polynomial-weight specializations. The package does not claim that every such
specialization is new. Its proposed organizing addition is the independently
regulated, all-factor inclusion–exclusion construction and the combined
all-index collision/Gamma/polylogarithmic consequences.

The incoming binary packages were not fully available to the source review.
Check their contents for equivalent statements before accepting any novelty
claim. The general first-q moment-prefix conjecture and the S6/S8 identities
are unchanged in status by this article. No arithmetic independence claim is
made. The general collision theory for singular periodic distributions is
also not settled by a mass-collision theorem for this family.

## Verification and changes

The two mathematical suites are independent in the limited sense explained in
their docstrings: one-dimensional Gamma quadrature, individual spectral
continuation, and small-mass coefficient expansions are compared. This is not
independent human peer review. Exact algebra and floating-point evidence are
separately recorded. No proof-assistant certificate or ball-arithmetic error
bound is supplied.

The sole concrete correction to an inspected repository file is an editorial
repetition in one known README version. See `integration/EDITORIAL_NOTE.md`.
All other warnings concern safe use of the new formulas and are not allegations
of errors in uninspected source material.
