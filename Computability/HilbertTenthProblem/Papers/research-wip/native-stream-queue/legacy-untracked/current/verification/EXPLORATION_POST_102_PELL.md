# Bounded Pell searches after the 102-operation certificate

This is an exploration note, not a new certificate or a lower bound.
The frozen reference is `round22_1980_composed_certificate.py`.
Fixed numerals are free throughout.

## Deleting the product U=wN^2

Replacing U=wN^2 by the supplied positive integer w would remove one
multiplication. It also removes two hypotheses of the current proof:

* the preliminary bound U>=N^2;
* the divisibility N^2|U, which transfers U=4^(2R+1) to the assertion
  that N, q, B, and b are powers of two, in that order.

The second issue is independent of the first. The later identity q=B^L
and B=Hb^2 does not exclude odd prime factors of b. Likewise, the
condition N^2|Y and the congruence

    floor((U+1)^(2R)/U^R) = binom(2R,R) modulo U

do not permit cancellation of the multiple of U unless N^2|U has
already been proved. No replacement argument has been established.

One simple possible odd-prime exclusion is false: the integer part
need not avoid small odd prime factors even when R is even. For R=8,
U=4^17, its value modulo 5 is

    sum(j=0..8, binom(16,8+j)*(-1)^j) = binom(16,8)/2 = 0 (mod 5).

This example only rules out that simple exclusion; it is not a
counterexample to the entire modified Diophantine system.

Using the existing UY register as the first exponential target would
restore N^2 divisibility through Y=sN^2. However, it changes the scale
of the exponential constraint: UY=4^(2R+1) together with the interval
Y approximately ((U+1)^2/U)^R would require U near the noninteger
root 7+4*sqrt(3) of (U+1)^2/U=16. This is not the freely selectable
exponential parameter of the established necessity construction.
No positive necessity construction for this variant was found.

## Eliminating the second Pell root by square completion

Write E=A-B and F=(A^2-1)-E^2. The existing E18--E19 pair is

    mu=q+kappa*E+rho*F,
    mu^2=(A^2-1)*kappa^2+1.

Given the shared norm coefficient A^2-1 and the already available
B-4, this pair costs 11 instructions: seven for E18 and four for E19.
The shift A=a0+4 is included in this count through E=a0-(B-4).

Eliminate mu and set t=q+rho*F. The exact replacement is

    t*(t+2*kappa*E)=F*kappa^2+1.

It costs 12 instructions with the direct factorization:

    E; E^2; F; rho*F; t; kappa*E; 2*kappa*E;
    t+2*kappa*E; t*(t+2*kappa*E); kappa^2; F*kappa^2;
    F*kappa^2+1.

Thus deleting the supplied root and its equality does not itself
save arithmetic. This is an exact accounting of this factorization,
not a claim that every circuit for the substituted polynomial costs
at least 12.

## Two equal norm constants

Introducing a positive root I for the signed Pell block is possible
in necessity, and its congruence is I+d=of. Combining the two norms
by difference of squares gives

    of*(d-I)=(A^2-1)*c^2-(G^2-1)*H^2.

With both products on the right already needed, this replacement
uses a subtraction, a multiplication, and a subtraction on the
right. The original second norm needs I^2 and one addition. The
direct combination therefore adds one instruction. Retaining the
original possibly signed root avoids an extra domain argument but
does not improve this count.

These lanes produced no reduction below 102.
