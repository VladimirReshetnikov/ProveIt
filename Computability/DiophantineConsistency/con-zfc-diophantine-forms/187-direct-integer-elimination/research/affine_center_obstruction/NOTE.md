# A restricted obstruction to improving the polynomial center by scaling

Prepared with AI assistance on 25 October 2026. This is an auxiliary exact
algebra result, not the principal consistency construction.

## Setting

Work in the polynomial ring Q[X,Y,k,U,b,c], with weights

    (X,Y,k,U,b,c) = (2,2,1,7,4,3).

Set

    A = XY + Y + 1,
    E = 1 + XY^2 k^2 + X^2 Y^4 k^2,
    Delta = A^2 - 1,
    G = E + Delta U^2 E^2,
    V = (1 + 2 Delta U^2 E)b - c.

These are the abstract whole-product quantities in source 178. The baseline
center has weighted defect degree 106. A natural attempt is to multiply the
root by a small polynomial scale and then retain more terms of its formal
square-root expansion. The following theorem rules out a degree improvement
from any nonzero affine scale in X and Y, even allowing rational coefficients
in the center.

## Theorem

For every nonzero r = aX + b0 Y + d in Q[X,Y] and every
C in Q[X,Y,k,U,b,c],

    weighted_degree(C^2 - 16 r^2 G V^2) >= 106.

In particular, neither r=X nor r=X+1 nor any other affine scale of these two
variables lowers the degree-106 abstract defect. The result is restricted to
this ring and this family. It is not a global lower bound for consistency
equations, arbitrary nonlinear scales, or centers using a different encoding.

## Proof

Introduce a formal parameter t by substituting
(t^2 X,t^2 Y,tk,t^7 U,t^4 b,t^3 c). The target 16GV^2 has leading term
64 X^14 Y^22 k^8 U^6 b^2 t^130. There is a unique formal Laurent square
root S with leading term

    8 X^7 Y^11 k^4 U^3 b t^65.

Its coefficients belong to Q(X,Y,k,U,b,c). They are recovered recursively:
at each new homogeneous degree, divide the still unmatched coefficient of
16GV^2-S^2 by twice the leading monomial of S. All coefficients of S above
weight 41 are ordinary polynomials. Write K=k^4 U^3 b. The parts containing
negative exponents in the three next relevant components are exactly

    S_41:   3 K Y^7/X,
    S_39:  -3 K Y^7/X^2 + 12 K Y^6/X,
    S_37:   3 K Y^7/X^3 - 15 K Y^6/X^2 + 15 K Y^5/X.

The accompanying script verifies these identities by exact rational
coefficient arithmetic from the displayed definitions. They can equivalently
be verified by squaring the recursively specified finite series and comparing
its coefficients through weight 102.

First suppose r is a nonzero constant. To obtain a defect of weight below
106, the polynomial C would have to agree with either rS or -rS through
weight 41. The nonzero term 3r K Y^7/X makes this impossible.

Now suppose r is nonconstant. The leading weight of rS is 67. To obtain a
defect below 106, C would have to agree with one of its two signs through
weight 39. At weight 43 the nonpolynomial part is 3 b0 K Y^8/X, so b0=0
is necessary. At weight 41 it is 3(d-a)K Y^7/X, so d=a is necessary.
Since r is nonconstant, a is nonzero. The remaining scale is a(X+1), but
its weight-39 nonpolynomial part is

    -3a K Y^6/X,

which is nonzero. This is again impossible for a polynomial C.

For completeness, the implication from the defect bound to agreement of
series is algebraic. Once the sign of the leading term is chosen, the other
factor in

    C^2-(rS)^2 = (C-rS)(C+rS)

has weight 65 for constant r and 67 for nonconstant r. The first unmatched
homogeneous coefficient of C-rS therefore gives the defect's leading weight
by adding 65 or 67. There can be no cancellation of that leading product in
the rational function field. This proves the theorem.

## Consequences and limits

Scaling by X clears the weight-41 term, but the next X^-2 term produces a
defect of weight 108 after scaling; the degree increase of the root offsets
the local cancellation. Scaling by X+1 cancels one further component but
leaves a defect of weight 106. Thus observing cancellation of only the first
offending monomial is not sufficient evidence of a lower-degree equation.

The theorem does not require any Pell or consistency assumptions. It is an
identity-and-divisibility statement about a fixed polynomial family. The
semantic calibration of a consistency equation lies outside its scope.

## Reproduction

    python3 -B verify_series.py --receipt CHECK.json
    python3 -B -O verify_series.py

The script uses only the Python standard library and has explicit checks;
it does not depend on removable Python assert statements.
