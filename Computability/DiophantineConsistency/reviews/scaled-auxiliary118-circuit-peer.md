# Independent review of the degree-118 auxiliary replacement

Reviewer: `/root/circuit_reduction`. ROOT authored the proof. I did not
author its replacement argument or the forthcoming graph/auditor. This
review covers the complete ordinary proof and its proposed graph
construction; it is not yet a review of a materialized 66-row graph or
its finite receipt.

Reviewed in full:

- `research/scaled-auxiliary118/PROOF.md`, SHA256
  `b2cb3b703da36bb33e1a3d26851d139a246010f1b2a39491927d6ea43031bd7f`.
- `research/carrier65-independent/PROOF.md`, SHA256
  `53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749`.
- The complete accepted 65-row graph
  `candidates/one-page-reversed-carrier65-2521/polynomial.json`, SHA256
  `408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff`.

The first proof is uniform in the four ports. The last graph supplies
the explicit operation schedule used to check the stated construction;
its reversed2521 native binding is not substituted for the sorted2501
native binding in any consistency claim.

## Positive zero sets

PASS. On all fourteen positive inputs, `Delta=(a+2)^2-1` is positive,
and its residues modulo four are exactly among zero and three.
Both products have the common factor
`Z=Delta*(f^2-Delta*i^2*c^4)`. Cancellation at a zero therefore gives
a product of five integer units. For the normalized strong factor,
the possible residues are square residues when `Delta=0 mod 4`, or
a sum of two square residues when `Delta=3 mod 4`. Neither admits
minus one. Thus `Z=Delta` follows at every positive zero of either
equation, without first assuming a sign or interpretation of any
other factor.

The exact identities

    A-S^2 = Z-Delta,
    Unew-U = (Z-Delta)*(V^2-y^2),
    pnew-p = P*Q*W*Z*(Z-Delta)*(V^2-y^2)

then prove both implications using the identity map on all fourteen
positive coordinates. In particular the proof covers noncanonical
solutions and does not need the auxiliary norm factor to have sign
plus one before establishing the transfer. It does not divide a
variable expression during evaluation or replace a source mask.
The inherited consistency interpretation still requires the complete
certified native tuple, as the proof states.

## Cost and degree

PASS for the construction and algebra. The accepted graph already
forms `scaled_f2=Delta*f2`. A single additional subtraction
`A=scaled_f2-Delta`, followed by changing the existing auxiliary
multiplication's coefficient from `S^2` to `A`, supplies the claimed
graph. Moving the existing `scaled_f2` producer earlier is a scheduling
change only. `S` and `S^2` stay live through the unchanged strong
factor. Thus the construction gives 37 multiplications, 16 additions,
13 subtractions: 66 integer-leaf operations on the same fourteen
inputs. A literal graph must still be checked separately.

I recomputed each displayed leading form from `a0=w*s*q0^4` and
`c0=s*(eta+zeta)*q0^3`. The apparent degree-22 terms in the main norm
cancel by the exact identity involving `Zeta=X+gamma*H`; its surviving
degree-18 form is `8*gamma*a0^2*c0`. The five factor degrees are
22, 18, 30, 2, 46, summing to 118. Multiplication of their leading
forms gives the displayed full degree-118 form, including its sign.
Its specified coefficient `-8*beta^68` is nonzero at every allowed
positive beta, so no specialization can lower the claimed exact
degree. This is a different polynomial with the same positive zero
set, not a pointwise equality with the degree-150 polynomial.

No mathematical correction is requested. The operation/degree tradeoff
is stated accurately; this review claims neither a global minimum nor
a new formal-kernel replay. No incoming executable was imported or run.
