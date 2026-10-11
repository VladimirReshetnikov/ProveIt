# Source and proof audit

Prepared 10 October 2026. Repository anchor:
`87c7db629552afbc2e803001526debe3430a31b0`.

## Sources actually inspected

Through the GitHub connector:

- canonical manuscript README and chapter inventory;
- `07-mixed-dougall-identities.tex`, including its first-resonance proof,
  mixed coefficient formulas, trigamma square and quadratic-tail theorem;
- `07-harmonic-gamma-coefficients.tex`;
- `04-S4-proof.tex`, including the exact-certificate construction;
- the concluding research/status portion of `10-discovery.tex`;
- incoming directory inventory and the initial intake-policy portion of its
  README;
- targeted repository searches for related harmonic and cubic-tail material.

Selected prior Library excerpts were consulted for duplication screening.
They were not treated as a substitute for the current canonical source.
The full contents of the incoming binary ZIPs were NOT inspected.

Primary external references:

- DLMF 16.4.9: the Rogers–Dougall 5F4 summation. Equation 16.4.6 is Watson's
  different 3F2 summation and is not the reference used in the final article.
- DLMF 5.8 and 5.11: Gamma products and uniform asymptotic expansions.
- DLMF 25.11 and 25.14: Hurwitz zeta and Lerch identities.
- Michael E. Hoffman, arXiv:1602.03399 (2016): sums of products of zeta tails,
  Euler depth-two identities, and the relevant MZV conventions. The PDF's
  formula page for Euler's identities was visually inspected.

## Proof provenance

The master Gamma identity at a=1 is a specialization of an existing result.
The article reproduces its necessary analytic derivation, including the
Laurent constant, rather than pretending that a finite coefficient test
proves the infinite sum.

The invariant recurrence, two-factor descent, symmetric cubic family,
quartic simplification, symmetric digamma cube, and cubic trace/primitive
formulas are derived in the report. Historical novelty of every consequence
has not been established by an exhaustive literature search.

The minimum-square map is proved by Tonelli and ordered equal-index blocks;
it is a weighted adaptation of known sums-of-tails methods.

## Findings and non-findings

The centered factor and subtraction in the inspected canonical mixed theorem
agree with the independent specialized calculation. No new mathematical
error in that inspected theorem was established.

Normalization safeguards are recorded in the article: include n=0, do not
confuse the weights 2n+1 and n+1/2, use product of roots -tau, keep the
exceptional linear subtraction intact, and combine removable expressions
before evaluating them.

The naive all-power extrapolation refuted in the report is NOT an existing
repository conjecture. The old rejected S8 vector is NOT the revised open
S8 candidate. No change to the Gaussian conjecture status is proposed.

## Verification record

596 exact assertions passed. 31 numerical diagnostics passed at 50 decimal
working digits. The largest scaled residual in the delivered numerical
suite is approximately 5.712e-35. That number describes floating-point
agreement, not a rigorous enclosure. No PSLQ or other integer-relation search
was used. No proof-assistant verification was performed.
