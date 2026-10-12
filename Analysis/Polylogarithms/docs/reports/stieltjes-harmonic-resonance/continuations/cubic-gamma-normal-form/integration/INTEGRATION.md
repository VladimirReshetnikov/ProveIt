# Proposed ProveIt integration

## Additive destination

Suggested report directory:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/cubic-gamma-normal-form/`

The supplied files can be copied into that directory without replacing
historical reports. The repository has not been modified by this delivery.

## Canonical manuscript placement

Place the main theorem in Volume III's differential-polynomial/Gamma-Appell
material after the canonical functional-monomial decomposition and finite-jet
Euler identity. The nonrecursive pure-u2 beta density should precede the
cubic theorem. The Hurwitz/Stieltjes and Lerch/polylog sections can then be
cross-referenced from the spectral endpoint-calculus material.

`insert_cubic_gamma.tex` is an additive theorem fragment with local labels
prefixed `cgnf:`. It assumes only that the host has `theorem`, `proof`,
`amsmath`, and `amssymb`; it does not import this report's preamble. For the
complete proof, import/adapt Sections 2–5 or cite the standalone report.
Do not label the fragment a self-contained proof of the all-index theorem.

## Source question status

The relevant question is in:

`.../continuations/affine-gamma-polarization/sections/11_questions.tex`

At the inspected source blob `981c58f36abb69568db38e8197fb8d8789e967f5`,
Question 1 requests all coefficients with `u3^2` and positive powers of
`u2`, with parity and endpoints retained. Theorem 4.1 and Corollary 5.1
of this delivery establish more: all powers `u3^n`, `n>=2`, while
Section 6 retains the full canonical endpoint and any high-derivative
remainder. The pure-u2 recurrence is credited to the predecessor.

Suggested status wording:

> The complete coupled next-Gamma sector is now proved. A cubic-background
> beta-density formula determines every coefficient with highest derivative
> index three, including arbitrary powers of u2 and u3, and gives a finite
> rational coefficient sum with parity zeros. The full primitive endpoint
> is retained by the canonical decomposition. The arbitrary-highest-order
> density formula remains conjectural; its finite checks are not a proof.

Question 2 is answered for all nonlinear sectors whose highest retained
index is at most three. Do not mark the unrestricted higher-index
polarization problem solved.

## Required overlap check

The incoming directory was inventoried but its binary packages were not
exhaustively read or replayed. Before declaring this a newest or globally
novel result, compare the actual contents of the current Gamma-normalization,
colored-moment, and polygamma/Stieltjes packages. Preserve alternative proof
routes and attribution rather than replacing them on the basis of a title.

## What not to promote

- Conjecture 9.1 (the arbitrary-highest-derivative density) is not a theorem.
- Numerical residuals are not interval-certified errors.
- Finite rational coefficient checks do not prove period independence.
- The cubic projection does not replace the full normal polynomial in a
  Gamma identity without its higher-derivative remainder.
- This report does not solve S6, revised S8, or the unrestricted unequal-tail
  optimal-prefix question.

## Editorial correction

In the inspected manuscript README, the paragraph about the complete
1,032-input first-letter X family, rank 1,008, and kernel dimension 24
appears twice consecutively. Remove the second duplicate only after
checking that the current file still contains it. The mathematical text of
the surviving occurrence should not be changed by that edit.
