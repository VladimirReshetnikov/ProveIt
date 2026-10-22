# Start-only degree and operation certificate

The literal source is `start_only_polynomial67.json`; the system source is
`start_only_system61.json`. Four fixed integer coefficients are named `Bm1`,
`Kconstant`, `MC`, `MF`, where `MF` denotes native MF + B - 1. They must come
from the separately specified Start-only compiler, not the earlier compiler
whose selector 1 was End. The 15 witnesses range over strictly positive
integers. Derived names are abbreviations, not additional quantified variables.

## Operation ledger

The polynomial has 67 arithmetic operations: 39 multiplications and 28
additions/subtractions. The six-equation system has 61 operations: 34
multiplications and 27 additions/subtractions. Constants are fixed integers;
exponentiation in their finite definitions is not an operation on unknowns.
All source rows and supplied ports are live. See `start_only_arithmetic_audit.json`
for SHA-256 receipts and independently authored arithmetic checks.

## Exact degree

Write q=(B-1)J+1, X=wq, Y=sq^3, E=XY, k=eta+zeta, c=kY+eta,
a=E+Y, H=4a+3, Delta=a^2+H, D=X+ac+gamma H,
C=q-F-alpha, and let R be the packed index. Let T denote the auxiliary quotient
and t the transport quotient. The six factors are

* N1 = tau^2 - L(L+k), with L=E*kY;
* N2 = D^2 - Delta*c^2;
* N3 = y^2 + Delta^2*i^2*c^4*(V^2-y^2), with V=c(Tf-1)-R*f^2;
* N4 = k-hE-R;
* N5 = (K+w)C+q-F-t(q-1);
* N6 = Delta*f^2-Delta^2*i^2*c^4.

The polynomial is N1*N2*N3*N4*N5*N6 - Delta.

Put Q=(B-1)J, and read the following as homogeneous leading forms:

| Factor | Degree | Leading form |
| --- | ---: | --- |
| N1 | 22 | -k^2*w^2*s^4*Q^14 |
| N2 | 18 | 8*gamma*k*w^2*s^3*Q^11 |
| N3 | 60 | i^2*k^6*w^4*s^10*Q^34*T^2*f^2 |
| N4 | 7 | -h*w*s*Q^4 |
| N5 | 2 | w*(Q-F-alpha)-t*Q |
| N6 | 46 | -i^2*k^4*w^4*s^8*Q^28 |

For N2, expansion must cancel the two a^2*c^2 terms first:
N2 = 2ac(X+gamma H)+(X+gamma H)^2-Hc^2.
This identity proves the degree18 upper bound as well as its displayed leading
form. The other rows follow directly from the definitions and R having degree4.

The resulting leading form of the polynomial is

-8*Q^91*h*gamma*i^4*k^13*w^13*s^26*T^2*f^2*(w*(Q-F-alpha)-t*Q).

The monomial
J^92*h*gamma*i^4*eta^13*w^13*s^26*t*T^2*f^2
has coefficient 8*(B-1)^92. It cannot cancel: the displayed term containing t
is unique in the last factor, and the eta^13 term in k^13 has coefficient one.
Since B>1, the coefficient is nonzero. The total degree is therefore exactly155
for every admissible compiler output, not merely at the test coefficients.

The system compares N1=N2=N3=N4=N5=1 and N6=Delta. Its residual degrees are
22,18,60,7,2,46. Their squared sum has exact degree120 because the sole
maximal-degree residual is N3-1. A straightforward evaluation has 78 operations:
61 for the circuit, 6 residual subtractions, 6 squarings, and 5 additions.

## Retained packed-index bounds with no End marker

Set G=q^2-C-qF=(q-1)(q-F)+alpha. Before the rank bootstrap, the unit-product
argument implies the transport factor is either +1 or -1 and C is nonnegative.
If C>=1 then F+C<q gives 2q-1<=G<=q^2-q-1.
If C=0 then q-F-t(q-1) is nonpositive. Its being a unit forces it to be -1,
so F+(t-1)(q-1)=2. Since q>=16, F=2 and t=1. Consequently G=q^2-2q, which
also lies in [2q-1,q^2-q-1]. Thus the old lower and upper packed-index estimates
continue to apply, including 3q+1<R<q^4-q^3. The later sign-recovery step forces
the transport factor +1, at which point C=0 is impossible. This is the needed
algebraic bridge; the independent compiler audit supplies the Start-only tableau
soundness and completeness argument.
