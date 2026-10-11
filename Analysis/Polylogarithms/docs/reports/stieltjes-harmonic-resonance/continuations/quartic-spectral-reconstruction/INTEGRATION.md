# Proposed ProveIt integration

This package is a research continuation of source revision
`73f18ef013d5b74eafc883efb2c15210642df12a`. It contains proposed additions;
it does not presume acceptance of a new theorem into the canonical manuscript.

## Suggested placement

Keep the complete package as a new continuation under the harmonic-resonance
research spine, for example
`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/quartic-spectral-reconstruction/`.
The title and paths may be adjusted to the repository's intake conventions.
Canonical integration should then share the section sources rather than copy
several divergent versions of a proof.

| Material | Natural canonical or report destination |
|---|---|
| Complete p=8 reconstruction and its ordinary polygamma identities | Unequal-tail/Bernoulli reconstruction development |
| Effective fixed-p theorem and explicit Padé multiplier | General Hankel reduction continuation |
| Quartic regular moments and generator | Following centered square and incoming cubic trigamma moments |
| Bilateral second and higher spectral defects | Following the several-quadratic-mass first derivative theorem |
| One-sided Stieltjes corrections and conjugate-linear defects | Polynomial-weight spectral factorization section |
| Dilogarithm/Gamma primitive | Anchored spectral and Stieltjes primitive development |

## Exact claim updates

### Reconstruction report, Q1

After accepting the complete order-eight theorem and its certificate chain,
replace the congruence-qualified collective status with:

> For every even q greater than 8, the first q centered even moments of the
> (8,q) tail product have full formal coefficient rank q.

Retain the historical theorem with its original qualification. The new proof
uses its mod-64 reduction, proves an infinite-range dominance statement, and
exhausts the remaining 31 finite indices with rational/modular arithmetic.
Do not revive the source's rejected simple valuation extrapolation.

### General unequal even orders

Add the effective eventual theorem for each fixed p=2a, including the exact
source determinant multiplier and the threshold termination proof. Do not
replace the unrestricted all-a, all-b conjecture with a proved status. The
explicit bounded finite remainder must still be resolved for every new a.
For p=10 the proved threshold is q>=3840; the unverified residual range is
6<=b<1920, apart from already established adjacent/gap-four cases.

### Reconstruction report, Q5

Close the quartic regular-parity formula/generator question. Preserve these
qualifications:

- The six-coordinate determinant is formal, not a proof of arithmetic independence.
- The zeroth quartic sum is Hoffman's 2016 evaluation, with the n=0 term restored.
- Fifth and higher powers, resonant Laurent constants, and minimal functional depth remain open.

### Quadratic-spectrum report, Q2 and Q7

Record both higher-derivative constructions:

- Q7: the several-quadratic second derivative is a sum of pairwise ordinary logarithmic corrections, with a one-dimensional resolvent integral and full confluent coefficients.
- Q2: the conjugate-linear problem uses spectral scale two and coefficient polynomials eta_k; the several-quadratic formula alone would not identify this normalization.

Keep the nonzero higher counterterms. In particular, bilateral zero values
at nonpositive integers do not justify deleting their spectral derivatives.
The one-sided Laurent correction uses the coefficient one degree above the
desired derivative because of the Hurwitz pole.

## Attribution/status correction in the same-direction report

The exact identification is
`C_{A,B}(q) = H_{q,1}(A,B) = Psi(A,B;q-1)`.
Here Psi is the Ihara–Nakamura–Yamamoto interpolant, published in
The Ramanujan Journal 67 (2025), article 1, DOI 10.1007/s11139-025-01045-2.
The repository's independent-orders and harmonic-gaps continuations already
cite and develop that all-depth family and its divided-difference kernel.

Suggested replacement for the attribution claim that the entire connected
double family is a new extension:

> The connected double family is the depth-two specialization of the
> established entire harmonic interpolant. We reproduce its normalization
> and kernel for use in the same-direction representations.

Revise further-research Q2 so it no longer asks for the already established
existence, entireness, shift/stuffle identities, or basic geometric kernel.
An explicit reduction problem on a specified mixed-index locus remains a
useful target. This correction does not invalidate the report's Barnes or
beta–Newton same-direction representation.

## Status boundaries

Gaussian S6 and the revised S8 candidate remain conjectural. The older
rejected S8 vector remains rejected. No failed search establishes arithmetic
nonreduction, and no numerical agreement is used to prove a period identity.
All high-precision diagnostics in this package remain separate from exact
finite certificates and analytic proofs.

## Reproduction gate

Run `python verification/run_all.py`, compile the article, and render the PDF
before accepting a modified version. `SHA256SUMS` identifies the delivered
artifact bytes. The source pin and critical source-member digests are in
`provenance.json`.
