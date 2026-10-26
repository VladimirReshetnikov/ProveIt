# Review of whole-product Pell centers

## Final four-scaled specialization

The subsequently selected endpoint uses the integer polynomial W4=W8/2
and root scale4, so its norm uses16G. This is legitimate without a rational
coefficient: Q3 is identically divisible by2 as an integer polynomial.
Here is a direct identity with the emitted factored formula. Put

`theta=U^2 b`, `S=QE`, `e2=(Yk)^2`,

`Rc=theta*(3E+e2)-(b-c)`,

`Sc=4E^2+3S^2+e2^2`.

Then

`W4=U*[2S Rc+A(4EV-theta Sc)]`

`=U*(4A Phi-2Q1-Q3/2)=W8/2`.

To verify the division-free identity, let
`R=S(E+e0)` and `S2=e2(2S-Ae2)`. Then
`Q1=S(b-c)+2theta(AE^2-R)` and `Q3=2theta(R-S2)`.
Substitute these into the middle expression and use `e0=E-AS`.
Every coefficient in the final displayed factored formula is integral.

All bounds and calibration arguments below therefore transfer by the
literal factor1/2: the center has the sign of V and

`3.5 AUE|V|<|W4|<4.5 AUE|V|`.

The scaled norm gives z=±4gy, and the same signed budget and canonical
positive witness construction apply. Its full top component is

`[P4]208 = 9*2^11 q0^88 w^18 s^52 i^10 k0^32 B0^2 (w^2-6s^2)`.

This mathematical review confirms the final center formula and degree.
The separately emitted literal DAG and its checker authenticate the stated
116-operation implementation.

## Original derivation and audit

This note records an independent ordinary mathematical audit of the root
agent's proposed whole-product centers and an exact sparse-polynomial
calculation. Literal endpoint costs require the separately emitted circuit.
No unmeasured operation count is asserted here.

## Definitions without hidden division

Use the compact construction's A,Y,k,U,b,c and put

`e2=k^2 Y^2`,

`e1=k^2 Y [1-2Y(Y+1)]`,

`e0=1+k^2 Y(Y+1)[Y(Y+1)-1]`.

Temporarily treat A as a formal indeterminate, keeping the other five
quantities fixed. Define the degree-six polynomial

`E(A)=e2 A^2+e1 A+e0`,

`Phi(A)=E(A)*[(1+2(A^2-1)U^2 E(A))*b-c]`.

At the actual A=Y(X+1)+1, these are exactly the existing E and EV.
For j=1,3,5 define Qj by **deleting** the terms of Phi of A-degree below j
and lowering every remaining A-exponent by j. This is a fixed finite
polynomial operation on a polynomial of degree six. After its coefficients
are printed or emitted, no division operation remains in the endpoint.

Define

`W8 = U*(8 A Phi-4 Q1-Q3)`,

`W16 = U*(16 A Phi-8 Q1-2 Q3-Q5)`.

For r=8 or16 use carrier center Wr directly:

`Z=M*(n-LB-Wr)+the unchanged remaining carrier terms`,

and final norm

`P=Q*(Z^2-r^2 M^2 G V^2)+(r^2 M^2 G-Z^2)`.

The lower-degree choice discussed here uses L=b^2.

## A uniform pre-sign bound

All facts below are available before B>=0 is established. In particular
X,Y>=32, b!=0, |b|>=1, f>2c, U>=c^2, and the auxiliary-index exclusions
give `|b|>8f^3-1/2>7f^3`. Also f>2c>16q^4>128.

Let Eabs(A) be the sum of the absolute coefficients of E evaluated at the
positive A, and similarly let Phiabs(A) be the coefficientwise absolute
majorant of Phi (with b,c,U evaluated as fixed integers).

Set t=(Y+1)/A. Then t<1/16. Since

`|e1|<2e2(Y+1)` and `0<e0<=e2(Y+1)^2`,

we have

`Eabs <= e2(A+Y+1)^2`,

`E >= e2 A^2(1-2t)`.

Consequently `Eabs/E < 289/224 < 2`.

The triangle inequality for polynomial coefficients gives

`Phiabs <= Eabs(|b|+c)+2U^2|b|(A^2+1)Eabs^2`.

Moreover `c+1<2U^2E` and
`|V|>(f-c)|b|>Delta U^2 E |b|`. Divide by `|Phi|=E|V|` to obtain

`Phiabs/|Phi| < 4/Delta+8(A^2+1)/Delta`

`=8+20/Delta<10`.

For every j, truncation immediately gives

`|Qj(A)|<=Phiabs(A)/A^j<10|Phi(A)|/A^j`.

Therefore W16 differs from `16AU Phi` in absolute value by less than

`10U|Phi|*(8/A+2/A^3+1/A^5) < AU|Phi|`.

The last inequality follows at A>=16 from
`10*(8/A^2+2/A^4+1/A^6)<1`. The same argument for W8 is even smaller.
Thus

`sign(Wr)=sign(V)`,

`(r-1)AUE|V|<|Wr|<(r+1)AUE|V|` for r=8,16.

No termwise sign assumption on Q1,Q3,Q5 is needed. This is significant:
b may have either sign before the consistency carrier is decoded.

## Signed carrier, integrality, and completeness

Scaling G by r^2 preserves the root-extraction argument. In the integer
norm equation, the new valuation contribution from r^2 is even. Thus
G=g^2, and rational adjacent-Pell descent gives `z=Z/M=±rgy` with integer y.
The strong pair, folded indices, and low-index exclusions are unchanged.

Since g<f/6 and AUE<3g/2<f/4, for r<=16 the preceding bounds give

`rgy+|Wr| < 9f|V|`.

For L=b^2, use `|V|<3f|b|/2`, `|b|>7f^3`, and f>128 to conclude

`rgy+|Wr| < 13.5 f^2 |b| < L/4`.

Thus B<=-1 would imply

`n < L/4-L+|b|/q^6 < 0`,

contradicting the positive coordinate n. The inverse correction is crucial:
its uniform bound rho<|b|/q^6 holds for every integer R.

Wr is an integer polynomial, so every later denominator, whole-product
projection, and dyadic-radix step has exactly the old fractional-part
relation. At canonical positive witnesses V>0 gives Wr>0, and

`n=rgy+Wr+(1+hL)t+rho-kappa-sigma`

is a positive integer by the retained bound
`g>kappa+sigma+|rho|`. This proves both directions of the new positive-zero
equivalence, relative to the same named parent calibration.

## Independently calculated exact defects

The exact sparse calculation treats A,Y,k,U,b,c as independent variables,
with weights 4,2,1,7,4,3. It expands

`Dr=Wr^2-r^2 G V^2`, with `G=E+(A^2-1)U^2 E^2`.

The whole defect has 594 terms for r=8 and 589 for r=16. Their weighted
degree is 106, and their complete highest weighted components are

`[D8]106 = 32 A^8 U^6 Y^8 b^2 k^8`
`          -192 A^6 U^6 Y^12 b^2 k^8`,

`[D16]106 = -768 A^6 U^6 Y^12 b^2 k^8`.

For comparison, the one-correction r=2 center has defect degree 114 and
leading component `4A^10 U^6 Y^8 b^2 k^8`.

With L=b^2, the uncentered carrier Z0 has degree21. The full-output
identity then gives term degrees122,177,208,152,72; 208 is the unique
maximum. Substituting the actual leading components and writing

`q0=beta J`, `k0=eta+zeta`, `B0=k0 sT-q0^2(q0-F)`,

the complete top forms are

`[P8]208 = 9*2^13 q0^88 w^18 s^52 i^10 k0^32 B0^2 (w^2-6s^2)`,

`[P16]208 = -27*2^16 q0^88 w^18 s^54 i^10 k0^32 B0^2`.

Both are nonzero polynomials for the actual positive beta. Hence both
have exact degree208. The 16-scaled center has a simpler leading form;
its extra Q5 correction does not lower the degree relative to the
8-scaled center. The literal circuit must decide which provides the
better arithmetic cost. Using bV would make the cross term have degree213,
so b^2 is essential for this degree208 endpoint.
