# Source audit and correction scope

## Inspected scope

The manuscript README, main document structure, portions of the integration chapter, lines 1-180 of the pointwise differentiation chapter, lines 1-200 of the reflected-moment and discovery continuations, incoming directory inventory, and lines 1-95 of the intake README were read. A later pinned read confirmed integration-chapter lines 12-60 and 75-150.

The observed head was `0e5ab2f60f8efe1f5dda7980c52bf86a9fd9bd02`. Individual observed blob hashes and read limitations are in `data/source_snapshot.json`. The entire repository and every incoming archive were not audited.

## A1. Search-basket wording: proposed correction

File:
`Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex`

Label: `integral:neg:psim2`

Observed wording:

> Basis atoms must be $\mathbb{Q}$-independent.

As a universal requirement this is too strong. Unknown independence is not necessary to search for a target relation or to prove an identity. A search with known dependencies can instead be carried out in a quotient or can explicitly distinguish target-bearing relations from old basket relations.

Proposed replacement:

> Remove or quotient known dependencies in the search basket, and distinguish relations involving the target from pre-existing relations among the basket atoms. Unknown numerical independence is not a prerequisite for an exact proof.

This is a methodological correction, not a refutation of the surrounding gamma-integral identities. The manuscript's later discovery chapter already treats formal versus numerical independence carefully.

## A2. Periodic differentiation: extension warning

The pointwise identity
`d^r/dx^r zeta(s,x)=(-1)^r (s)_r zeta(s+r,x)`
and the Stieltjes derivative tower are valid as stated.

They do not imply that finite-part extension commutes with differentiation. The periodic Hurwitz residue at s=1 is `1-delta_0`, not the pointwise scalar residue `1`. The correct law is Theorem 6.1 of this report.

Example:
`FP integral psi(x) psi'({x+a}) dx = J00'(a)+psi'(1-a)`.

The extra term is essential. No claim is made that the inspected manuscript already stated the incorrect no-contact formula.

## A3. Normalization and domain guardrails

Finite parts use right-endpoint coordinates exactly x and x-(1-a), with no scale change. Do not evaluate the separated-singularity formulas at a=0. Combine meromorphic beta summands before substituting a removable singularity. Convert base-point primitives to zero-mean primitives before applying the lift.

The existing denominator-five log-Gamma correction is already in the inspected chapter; this report does not claim it as a new discovery or undo it.

## A4. Numerical differentiation diagnostic

In the tested environment, naive tiny-step generic derivatives of a complex polylogarithm at integer order and a generic Hurwitz call at spectral order zero lost digits. Direct Hurwitz derivative arguments and rational Fourier decomposition resolved the observed discrepancies. This concerns those numerical calls, not the correctness of the analytic functions or a universal library defect.

## Unresolved and unclaimed

S6/S8; numerical period independence; a canonical collision conversion formula; all triple-factor reductions; global priority; proof-assistant verification; certified numerical interval enclosures.
