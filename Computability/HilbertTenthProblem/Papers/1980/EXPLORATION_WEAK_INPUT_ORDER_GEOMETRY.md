# The weakened-input 79-operation order geometry is false

This note preserves an exact counterexample to one proposed change
of the proved 80-operation radix-eight history system. The proposed
arithmetic list has 79 operations, but it admits positive endpoints
outside the intended relation. The 80-operation source and proof
remain unchanged.

## 1. The proposed replacement and its exact arithmetic count

The valid source uses W=v^3, q=v*quot and I+alphaI=v. The proposed
replacement supplies positive W and d_geom and uses

    q=W*quot,
    W-1=7*d_geom,
    q-1=H*(W-1),
    I+alphaI=W.                                      (1)

Once q is known to be a power of two, the divisor equation and
the order of two modulo seven correctly prove W=8^m and q=W^t.
Thus the failure below is not a false power or rectangle geometry.
The issue is the weaker bound on the initial row.

The geometry in (1) costs five operations, replacing the old six.
All other equations and the same local bound are retained:

    B=8C,
    15B+4Y=C+2U+3V,
    C+2U+3V+alpha=q,
    I+WY=C+qF,
    P=U+qV+q^2Y+q^3(B+H),
    L=q^6, D0=q^10, 7lambda+1=L,
    r=(L-P)*7lambda+6lambda.                       (2)

The retained ten Pell equations are unchanged, with scale D0.
The exact modified list in
`../verification/explore_two_auxiliary_weak_input_geometry.py`
has 79 primitives: 45 multiplications and 34 additions/subtractions,
30 positive unknowns, 20 source equations, and positive parameters
I,F. It verifies all source residuals, including the auxiliary norm
correction. This arithmetic count is for a semantically refuted
candidate, not an improved history certificate.

## 2. An exact all-positive outer tuple

Take the following positive integers:

| Quantity | Value |
|---|---:|
| q | 1073741824 = 8^10 |
| W | 32768 = 8^5 |
| quot | 32768 |
| H | 32769 |
| d_geom | 4681 |
| B | 19108416 |
| C | 2388552 |
| Y | 17039432 |
| U | 151031872 |
| V | 16777224 |
| I | 29256 |
| F | 520 |
| alpha | 718957856 |
| alphaI | 3512 |

All eight displayed geometry, local, bound and time equations in
(1)--(2) hold exactly. The four packed fields Y,U,V,B+H are Boolean
radix-eight words below q. The packed integer is

    P=23695639330513859234295456141971520.

With lambda=(q^6-1)/7 and r defined by (2), exact integer evaluation
gives

    0<P<q^4,
    r=0 modulo 2,
    popcount(r)=300,
    q^10<r<q^15,
    q^20>2r+1.

Since q=2^30, D0=q^10=2^300. The popcount identity therefore gives
D0 dividing binom(2r,r), with precisely the correct mask threshold.
The failure survives the complete Boolean mask and its scale.

The radix-eight digits, listed from the least significant upward, are

    I: [0,1,1,1,7],
    B: [0,0,1,1,1,7,0,1,1,0].

In particular I is a positive non-Boolean parameter, and the second
five-cell source row starts with digit seven. The intended endpoint
relation of the 80-operation theorem derives Booleanity of I and F
from its source equations; it does not assume it as an external
promise. This tuple therefore lies outside that relation.

The mechanism is explicit. Subtracting the genuine row-start word H
from Boolean T=B+H allows row-start digits zero, six or seven. The
first zero start comes from B=8C. Under the weakened I<W bound,
the highest digit of c0=I may be seven, permitting the next B row
to start with seven. The local arithmetic then has carries at this
seam. The original input guard makes I<W/8, so that digit must be
zero before any local-rule decoding.

## 3. Extension to every positive Pell witness

The counterexample is not limited to its outer equations. Put
n0=q^5, so D0=n0^2. The exact bounds above give n0>=64 and
n0<=r<2n0^3. We have even r and D0 dividing the central binomial
coefficient. These are exactly the hypotheses of the canonical
positive construction in `BASE_TWO_PELL_90_PROOF.md` after omitting
its second exponent/index block.

In detail, choose

    J=2r+1, U_pell=2^J,
    Y_pell=floor((U_pell+1)^(2r)/U_pell^r),
    w=U_pell/D0, s=Y_pell/D0,
    a=Y_pell*(U_pell+1), A=a+2, Dpell=A^2-1,
    c=psi_A(J), d=chi_A(J),
    k=psi_(2*U_pell*Y_pell^2+1)(r+1).

The power-of-two and binomial conditions make w,s positive integers.
The proved strict ratio gives positive eta=c-Y_pell*k and
zeta=k-eta. Set tau=(chi_(2*U_pell*Y_pell^2+1)(r+1)-1)/2 and
h=(k-r-1)/(U_pell*Y_pell); the same norm and index identities
make them positive integers. The first exponent congruence gives
the positive quotient gamma.

For the relaxed and half-parameter witnesses, use
`HALF_PARAMETER_PELL_92_PROOF.md`: set m=2cJ,
f=chi_A(m), R=Dpell*psi_A(m), i=R/c^2,
u=chi_R(J)/R and y_aux=psi_R(J). Even r gives J=1 modulo four,
so u=J modulo c and u=c modulo f. Hence
j=(u-J)/c and o=(u-c)/f are positive integers, and the retained
auxiliary equations hold. This constructs all 17 positive Pell
unknowns. Together with the 13 positive outer unknowns it supplies
a full positive solution of the modified 20-equation system.

The regression does not materialize these enormous Pell integers.
It checks their exact hypotheses; the cited general positive
construction proves their existence.

## 4. The precise boundary of the obstruction

An independent Boolean condition on I would remove this particular
failure. Then the top digit of c0=I would be zero or one, while the
corresponding next B row start belongs to {0,6,7}; it must therefore
be zero. The remaining causal proof can proceed using masked Y.
However, the refuted candidate contains no such Boolean test on
its arbitrary positive input parameter. Adding it, or obtaining it
from another proved input compiler, is a separate change with its
own accounting obligations.

`../verification/explore_two_auxiliary_weak_input_geometry.py` and
its JSON receipt verify the complete altered arithmetic list, every
outer equality at this tuple, all masked fields and range conditions,
the invalid endpoint digits, and the exact central-binomial valuation
through popcount. The original 80-operation system is preserved.
