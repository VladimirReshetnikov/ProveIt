# A local degree floor and a rejected shortcut

## The remaining bottleneck is the strong-root defect, not the weight

For the current registers, replacing L=k(T+F+alpha) by any polynomial weight of total degree at most three leaves the exact degree 912 unchanged. The two smallest formal norm factors are controlled by

    leading(Kscale*I^2/(2Cf))=2*q0^6*I0,

of degree 17. This is larger than the degree-16 main center. Any degree-three weight affects only degrees at most sixteen in the full scaled transport coordinate.

A polynomial weight of degree four still cannot cancel that degree-17 term. Its only new degree-17 contribution is

    -Kscale0*L0*Bt0=-4*q0^6*a0*L0*Bt0.

It is divisible by X, since a0=X*q0^3*s. The strong-defect term 2*q0^6*I0, with I0=i*(eta+zeta)^2*q0^6*s^2, is not divisible by X. Their sum is a nonzero polynomial. Thus the same degree 912 remains for every degree-four weight as well, whether or not that weight satisfies the arithmetic positivity and completeness requirements.

This is only a local obstruction for changes to the weight with the other registers held fixed. It is not a lower bound for other centerings, coordinates, norm encodings, or Diophantine consistency equations. A useful next direction is an arithmetic transformation that deals with the rational strong-root correction I/(2(a+2)) without multiplying I by a new degree-five factor or invalidating the main-root residue congruence.

## Why simply exchanging the strong root and its ordinate is not proved

Keeping f as a supplied variable and eliminating i would replace the strong radicand by (f^2-1)/(Delta*c^4), greatly lowering apparent degree. But rational root extraction alone would not make i integral. A rational i does not supply c^2 | I, and that divisibility is used before the signed auxiliary-index lemma recovers p=R. Inferring its integrality only after rank or main-residue recovery would be circular. The present packet makes no claimed endpoint based on this shortcut.

## Four-polynomial-radicand identity

For four polynomial radicands with elementary symmetric functions sigma1,...,sigma4, set

    x=z^2-sigma1,
    K=x^2-4sigma2,
    E=K^2+64(sigma4-z^2*sigma3),
    B=K-4z^2*x.

Then their sixteen-factor signed-sum norm is E^2-256sigma4*B^2. This is useful for some four-root circuits without rational radicands. Clearing the auxiliary denominator in this packet makes that schedule two operations longer (128 rather than126), so it is not the delivered circuit.
