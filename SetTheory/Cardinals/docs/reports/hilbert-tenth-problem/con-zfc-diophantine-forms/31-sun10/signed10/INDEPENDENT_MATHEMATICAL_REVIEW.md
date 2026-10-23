# Independent mathematical review of the signed-ten improvements

This review checks the three local changes to Sun's ten-integer construction.
The fixed instance is the complete 121-by-8801 tuple; no coefficient port is
exchanged separately. The implementation inspected is
`output/con_zfc_synthesis/signed10/build_signed10.py`, primary structural
weight scheme, degree-five merger.

## Coprime positivity merger

Write b=1+3f, O=f^2*l^2*Delta, d=3O-4 and

    J=1+d*b^2*z^2,    r0=b*J.

The integer b is nonzero, and gcd(b,J)=1. J cannot vanish: if J=0,
then b^2 divides 1, so b=1 (since b=-1 is impossible modulo 3).
Thus f=O=0 and J=1-4z^2, which is never zero. Consequently r0 is
universally nonzero.

If r0 is a square, coprimality makes |b| and |J| squares. A negative
square is congruent to 0 or 2 modulo 3, whereas b=1 modulo 3.
Therefore b is a positive square and J is a positive square.
If z is nonzero and O<=0, then d<=-4 and J<=1-4b^2z^2<=-3,
a contradiction. Thus the one square condition recovers b square and O>0.

In the forward direction, choose the source witness with f>=2. Its
positive bridge has Delta>0 and l!=0, so O>=4. Then d>0 and d=2 modulo3,
hence d is nonsquare. A nontrivial Pell solution u^2-d*v^2=1 can be
chosen with b dividing v, by taking a positive power of a Pell unit whose
matrix is the identity modulo b. Set z=v/b>0. The bracket J=u^2 and b
are both squares, hence r0 is a square.

## Required source freedom is explicit

Sun 2021, Theorem 3.1, equation (3.1), states a forward implication
with `for every Z>0 there exists f>=Z`. In its proof the base is selected
as a sufficiently large even power of p satisfying the required residue.
Taking Z=2 is therefore permitted.

Sun 2021, Theorem 4.12, begins with fixed b,g,P,Q,X,Y. Its construction
selects w,l,h,k and does not change b or f. Sun 2026, Proposition6.1,
uses precisely this construction with p=P=2,Q=1, after selecting f,g
from its Proposition2.1. Therefore the source condition f>=2 survives
all later bridge choices. The source positivity proof gives Delta>0.

Sun 2026, Theorem4.1, gives a positive xi divisible by ANY prescribed
positive integer N. For that xi it supplies every residue class of y
modulo xi while retaining D*F*Istar square. Take N=z and x=xi/z.
The subsequent selection of the quintic root residue q+y modulo xi is
therefore permitted for the same xi; no new variable is needed.

Primary sources inspected directly:
- https://arxiv.org/html/1704.03504v7 , Theorems3.1 and4.12.
- https://arxiv.org/html/2609.01594v2 , Proposition6.1 and Theorem4.1,
  plus the positive direction of Section7.

## Structural signed weights

When z!=0, the above r0 also satisfies |r0|>1. Indeed r0=+1 or-1
would imply |b|=1, hence b=1,f=O=0 and r0=1-4z^2<=-3.
The case r0=0 was already excluded without assuming z!=0.

Put p0=U^2*V and r1=(p0^2-4)*K^2+4. For all real p0,K,

    |r1| <= (p0^2+4)*K^2+4 <= (p0^2+K^2+2)^2,

where the difference in the second inequality is

    p0^4+K^4+p0^2*K^2+4p0^2 >= 0.

Thus w1=r0 and w2=r0*(p0^2+K^2+3) obey

    |w1|>sqrt(|r0|),
    |w2|>sqrt(|r0|)+|w1|*sqrt(|r1|).

These are strict even before positivity has been recovered and when the
weights are negative. The largest differing nonzero root in any two
signed sums dominates all preceding terms in absolute value. The triangle
inequality works for imaginary as well as real roots. Hence a rational
signed sum of sqrt(r0), w1*sqrt(r1), w2*sqrt(r2) forces all three
radicands to be integer squares by the finite-Galois sign argument.

The primary code uses radicands [r0,R2,D*F*Istar] in exactly this order
and the two displayed weights. Its collected three-root norm agrees
with the signed16 norm identity.

## Quintic merger and zero cases

The denominator S=2A-5 is never zero. With
Pi(T)=(T^3-T-1)*(T^2+23), Theta=S^5*Pi(T/S+y) never vanishes, since Pi
has no rational zero. With Sigma=xi*S^5, Sigma=0 makes the final
three-root norm equal Theta^8, which is nonzero. Thus every zero of the
final polynomial has xi=z*x!=0, so all the preceding z!=0 estimates
are available before the root-separation argument.

The homogeneous quintic divisibility lemma proved in the signed16
section recovers S|T and xi!=0 from Sigma|Theta. Its completeness uses
only a root of Pi modulo |xi|. Sun's full interpolation theorem supplies
the required y residue for that same Lucas certificate, as explained
above. Nothing in the interpolation proof depends on Sun's original
sextic intersective polynomial.

## Conclusion

The coprime positivity merger, quintic substitution, and structural
signed weights are valid, including the A1=0, f=0 and z=0 edge cases.
The inherited reverse bridge is applied only after b square, O>0,
xi!=0, D*F*Istar square, R2 square and S|T have all been recovered.
This is an ordinary mathematical audit, not a new formalization or an
independent audit of every original Lucas theorem.
