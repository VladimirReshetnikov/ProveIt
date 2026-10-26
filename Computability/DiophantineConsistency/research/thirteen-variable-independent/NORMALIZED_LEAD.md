# A further strong-factor normalization: prospective13/71/128

This is a separately scoped arithmetic lead, not a materialized graph or
new main page. It uses the complete thirteen-positive-variable polynomial
and witness maps in PROOF.md, corrected SHA256
`d2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8`.
The accepted native binding remains the full2471 tuple. The69/174 and
70/140 literal graph audit is a separate work item.

Retain all thirteen unknowns and all abbreviations except the strong
factor. Since `S=b*i*Delta*c^2`, define instead

    Zbar=f^2-Delta*(b*i*c^2)^2,
    pbar=P*Q*U*Zbar-1.

The full polynomial-ring identity is

    p=Delta*pbar,

because Z=Delta*Zbar. Delta is strictly positive on every positive input,
before any equation or native decoding. Thus p and pbar have exactly the
same thirteen-coordinate positive zero set. Every already proved map for
p applies unchanged. This normalization uses no extra sign lemma and
does not merely hold on canonical witnesses.

In the proposed70-row schedule, retain `hi=b*i`, `Dc2=Delta*c^2`,
`scaled_f2=Delta*f^2` and `Theta=scaled_f2-Delta`. Delete the two products
forming S and S^2. Replace them with three products

    hi2=hi*hi, intermediate=hi2*Dc2,
    strong_term=intermediate*c^2.

Replace the old strong subtraction by `Zbar=f^2-strong_term` and the
last subtraction by product minus1. All other rows stay unchanged.
The schedule adds one multiplication overall: prospective71 operations,
40 multiplications,16 additions and15 subtractions. All removed rows are
used only by the old strong factor after the scaled auxiliary replacement.
A complete graph audit must independently check these exact dependency
and liveness claims before accepting a finite evaluator.

The exact degree drops by12, the degree of Delta, because the polynomial
ring is an integral domain and p=Delta*pbar. Equivalently the strong
factor now has leading form

    -i^2*w^2*s^6*k0^4*q0^22

of degree36, with q0=beta*J and k0=eta+zeta. Multiplying the complete
leaders of P,Q,U gives the full degree128 form

    -128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^10*T^4
        *(q0-F-alpha)^2.

Its selected coefficient on
`J^71*gamma*i^2*eta^11*w^10*s^19*f^10*T^4` is `-128*beta^71`.
This is nonzero at the actual positive beta. All fixed ports are identical,
and the operation/degree tradeoff is70/140 to71/128 with13 positive inputs.
The analogous fourteen-variable scaled equation has prospective67/106,
from66/118, by the same normalization and one-extra-product schedule.
Neither new graph, complete page nor unrestricted lift is supplied here.

This identity is elementary arithmetic. Its consistency interpretation
continues to use the complete previously stated native and syntactic
contracts; it is no new formal-kernel replay or global-minimum claim.
