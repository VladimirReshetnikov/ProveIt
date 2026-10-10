# Evidence and dependency ledger

This ledger distinguishes a theorem's mathematical argument from its optional
numerical illustration. The reported novelty scope is relative to the pinned
manuscript, not an exhaustive literature-priority claim.

| Result | Main dependency | Proof-bearing finite data | Status |
|---|---|---|---|
| Appell–Laplace representation and n-zero bound | Mellin representation, reciprocal-gamma product, variation/Rolle argument | None | Inherited framework; proofs reproduced |
| Universal endpoint block, Theorem 3.1 | Classical Erdelyi expansion and exact gamma-pole cancellation | None | Analytic deduction |
| Finite-part polylogarithm identities | Theorem 3.1 at a=1 | None | Proved; not new arithmetic independence |
| C^(k-1), not C^k regularity | Exact convergent endpoint expansion | None | Analytic proof |
| Low-order simple-root endpoint velocity | Exact expansion and implicit continuation | None; hypothesis is a simple endpoint zero | Conditional theorem with explicit hypothesis |
| Eventual all-branch strict decrease, Theorem 5.1 | Mixed c/rho gamma-concentration estimate and simple Appell roots | None | Analytic proof, existential k threshold |
| All-index small-positive-rho count, Theorem 6.1 | Elementary endpoint polynomial, analytic local unfolding, global exclusion | None | Analytic proof; rho=0 multiplicities separate |
| Complete n=2 branch geometry, Theorem 7.2 | Power-series variation and multiplicity bounds | Negative anchor at a=1.3, positive anchor at a=1 | Proof with exact rational sign anchors |
| Unique n=3 left fold, Theorem 8.1 | Nested negative sets, global three-zero bound, analytic fold | Negative anchor at a=1, positive separator at a=1.5 | Proved only in stated left interval; positive rho below threshold |
| Sharp n=5 count, Theorem 9.1 | Complete critical-point descent and upward persistence | Endpoint brackets plus whole-bracket predecessor signs | Computer-assisted theorem with exact interval certificates |
| Numerical fold and minimum coordinates | mpmath quadrature and root finding | None | Diagnostics only, not isolating intervals |
| No extra n=3 outer pair below the fold | Not established | None | Explicitly conjectural |
| Effective least all-branch monotonicity threshold | Not established | None | Open question |

## Exact certificate audit

The Euler–Maclaurin remainder is proved before it is implemented. Logarithms
are enclosed by rational atanh series. Interval arithmetic uses integer fixed
point with outward rounding at every operation. The reference configuration
uses scale 10^55, 72 logarithm terms, N=32 and M=16.

The n=5 proof first obtains all five roots of F_(5,3)^1 by five sign-changing
brackets and the global bound. The code then certifies F_(5,2)^1 on the entire
five brackets, with signs +,+,-,+,-. This determines exactly three roots of the
predecessor by strict monotonicity between all known critical points. At the
three critical points of the next predecessor, whole-bracket signs are -,+,-.
The process then determines exactly three roots of F_(5,1)^1. No critical
point is replaced by a floating-point approximation in this proof.

There are 35 exact sign assertions. The regression report counts 10,972
assertions, including replay of those same 35 certificates; it is not a claim
of 10,972 independent theorems or a proof of implementation correctness.
Optional symbolic tables have 42 checked formal equalities. None of these
checks is proof-assistant verification.

## Boundary and scope audit

At n=3,k=1,rho=0 there are two distinct positive zeros: a=1 (double) and a=e^3
(simple). For sufficiently small *positive* rho, only the latter is real.
The interior fold theorem therefore uses 0<rho<rho_c, not 0<=rho<rho_c, in
its no-left-zero statement. This distinction is retained in both article and
integration fragment.

The article's n=3 fold theorem does not rule out a separate outer pair at all
intermediate parameters below the threshold. That stronger global statement
is explicitly conjectured. The exact n=5 theorem concerns the classical
endpoint rho=1, not uniform saturation throughout the entire deformation.

## What was not done

No full audit of every manuscript chapter, no proof-assistant formalization,
no external peer review, no exhaustive literature-priority search, no complete
repository rebuild, and no remote repository modification were performed.
The source's already-proved global bound and eventual asymptotics are retained.
The mixed S4 identity and numerical period-independence questions are untouched.
