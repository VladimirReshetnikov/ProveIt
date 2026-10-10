# Audit and corrections proposed for integration

## Findings established in this delivery

**Numerical order-derivative hazard.** In the tested mpmath 1.3.0 / Python 3.13.5 environment, at 40 decimal working digits and exact argument i, default differentiation of Re(polylog(s,i)) at s=2 disagrees with the exact cyclotomic reduction by approximately 2.33945455584e-12 for the first derivative and 2.44970539683e-16 for the second. Direct values agree. The minimal reproducer and output are included. Recommended correction to a future verification workflow: compare against exact cyclotomic/Hurwitz reduction before treating nominal working precision as achieved derivative accuracy. This does not establish that any particular upstream claim used the failing path.

**A fixed finite-part constant.** The endpoint-subtracted digamma correlation contains -2*zeta(2), not zero. A negative control verifies the missing-constant discrepancy. The cutoff and convergent forms prove the constant analytically.

**Coincident endpoint normalization.** A merged product requires subtraction of epsilon^-1 E_(m+n)(log epsilon), in addition to the two logarithmic terms. The remaining constant equals the collision-renormalized translated limit. This is a new formula's normalization requirement, not an allegation that the repository already printed the wrong one.

**Removable Gamma/Hurwitz poles.** Expanding terms of a cancellation separately at u+v=0 is invalid. The regular Gamma-ratio expression in the article gives a stable symbolic route. The elementary endpoint limit (1-c^-u)/u is +log(c); the sign is important.

## Existing material that should not be misreported

The inspected current S4 source contains an analytic/exact-certificate proof. Older descriptions of S4 as merely numerical are superseded. The integration chapter already corrects an overly broad Clausen-only denominator-five extrapolation by retaining a Dirichlet derivative; this report does not remove that correction. Single Stieltjes antiderivatives and the unshifted quadratic log-Gamma moment are classical, not claimed as new here.

No mathematical theorem in the selected upstream material is declared false in this delivery. The review is not a clean bill of health for the whole repository.

## Explicit review limits

Selected manuscript portions and metadata were read, rather than every chapter. Incoming filenames and intake instructions were read; binary ZIP contents were not audited. No proof-assistant formalization, certified interval quadrature, complete priority search, S6 proof, or period-independence proof was performed. The supplied evidence records distinguish exact finite algebra, ordinary analytic proofs, and numerical diagnostics.
