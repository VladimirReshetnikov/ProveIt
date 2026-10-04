# An unbounded genuinely scaled first/main obstruction family

This preserves the intermediate subsystem argument. The outer/input
obstacle listed below is subsequently completed in FULL_COUNTERFAMILY.md
using a related dyadic family and factorial CRT construction.

This is a subsystem theorem, not a full candidate counterexample.
It disproves the proposed recovery of the deleted congruence from only
the two Pell norms, strict ratio, main projection, genuine X=wq/Y=sq^3
scales, p=3 modulo4, and the actual scalar packed-index bounds.
The exact fixed-mask packing, transport and input equations remain open.
The full inherited compiler-numeral contract is not asserted here.

All variables below are integers. To avoid colliding with source a,
call the independent parameter r. Take odd r>=5, r=1 modulo4, and set

    p=r(2r+1), d=r^2, n=(3r^2+r)/2,
    v=((2r+1)(r+1))/2-1,
    X=2^p, Y=2^v,
    a=Y(X+1), A=a+2, Delta=A^2-1,
    P=2XY^2+1, E=XY, H=4a+3,
    D=chi_A(p), c=psi_A(p),
    tau=chi_P(n), k=2psi_P(n).

Then p=3 modulo4, d=2n-p>=25, and both Pell norms hold exactly.
Both strict ratio slacks eta=c-kY and zeta=k-eta are positive.
The main quotient gamma=(D-ac-X)/H is an integer greater than1.
Thus the literal first/main subsystem has positive eta,zeta,tau and
a positive split gamma=rho+sigma. That arbitrary split is not claimed
to satisfy the input norm, which constrains rho separately.

## 1. Exact dyadic balance and strict ratio proof

The exponents satisfy

    p(p-n)=d(v+1), d=2n-p.

Put L=2XY=2^(p+v+1), M=4XY^2=2^(p+2v+2). The preceding equality
is exactly

    L^(p-1)/(2M^(n-1))=Y.                         (1)

Also

    2A-1=L(1+1/X+3/(2XY)),
    2A=L(1+1/X+2/(XY)),
    2P=M(1+1/(2XY^2)), 2P-1>M.

Elementary Pell bounds give

    c>=(2A-1)^(p-1), k<=2(2P)^(n-1),
    c<(2A)^(p-1), k>=2(2P-1)^(n-1).

Because p>n and1/X+3/(2XY)>1/(2XY^2), the first pair and(1)
give c/k>Y. For the upper bound put epsilon=1/X+2/(XY)<2/X.
As p>=55, (p-1)epsilon<2p/2^p<1/2. The elementary binomial bound
(1+epsilon)^m<=1/(1-m epsilon) for m epsilon<1 gives

    0<c/k-Y<4p*Y/X=4p*2^(v-p).                    (2)

Now p-v=r^2-(r-1)/2. For every odd r>=5,

    4r(2r+1)<2^(r^2-(r-1)/2).

At r=5 this is220<2^23. Increasing r by2 multiplies the right side
by2^(4r+3), while multiplying the left side by less than4; induction
proves the inequality. Hence(2) is less than1, establishing

    Y<c/k<Y+1.

These are uniform exact inequalities, not floating-point evidence.

## 2. Main projection and missing-index defect

The main projection sequence z_j=chi_A(j)-a psi_A(j) obeys
z_j=2^j modulo H, as proved in PROOF.md. Here X=2^p exactly, so
gamma=(z_p-X)/H is integral. Also z_p=2c-psi_A(p-1)>c, and
c>=psi_A(3)=4A^2-1>X+2H. Therefore gamma>2, so positive
rho,sigma with sum gamma exist.

Since P=1 modulo E, k=2n modulo E. With E>d>1,

    (k-p-1) mod E=d-1=r^2-1>0.

Consequently no integer h can restore k=p+1+hE in this subsystem.

## 3. Genuine source scales and every scalar packed-index bound

For any dyadic q=2^t>=16, choose

    r=q^2/2+1.

Then r is an odd integer congruent1 modulo4. Both p>=t and v>=3t,
so w=X/q and s=Y/q^3 are positive integers. Also

    p=q^4/2+5q^2/2+3,
    (2q-1)(q^2-1)<p<q^4-q^3.

For the lower bound, subtracting yields
q^4/2-2q^3+7q^2/2+2q+2>0 for q>=16. For the upper bound,
q^4/2-q^3-5q^2/2-3>0 for q>=16. These prove the exact scalar
inequalities used by the full-source pretyping argument, with R=p.

For example q=16 gives r=129,p=33411,n=25026,d=16641,v=16834.
The main/first Pell coordinates for this example are intentionally not
materialized. The preceding uniform proof certifies the subsystem.
In particular, it would be misleading to identify these scalar bounds
with the literal packed R equation: that equation is not checked.

The smaller exactly materialized fixture r=5 has

    q=16,p=55,n=40,d=25,X=36028797018963968,Y=4294967296,
    w=2251799813685248,s=1048576,
    (k-p-1) mod XY=24.

It meets the true scales but fails the scalar R lower bound. It is used
only as a modest exact check of the same ratio/projection phenomenon.

## 4. Formal auxiliary completion is also available

This section is a parametric existence proof, not a materialized tuple.
It does not impose any packing, transport or input equation.
Because p=3 modulo4, the standard canonical minus auxiliary construction
can be carried out at these exact A,c,p:

    m=2cp, f=chi_A(m), iN=psi_A(m)/c^2,
    S=Delta*psi_A(m),
    y=psi_S(p), V=chi_S(p)/S,
    o=(V+c)/f, j=(V+p)/c,
    T=(o+pf)/c.

All displayed quotients are positive integers. The expansion of
(chi_A(p)+c sqrt(Delta))^(2c) gives c^2|psi_A(m).
The odd-index polynomial Q_((p-1)/2) gives V=-c modulo f and
V=-p modulo c because (p-1)/2 is odd; it also gives integer V.
Positive Pell growth gives V>c>p, hence o,j>0. Since f^2=1 modulo c,
multiplying of+p=c(j+1) by f gives c|(o+pf), hence T>0.

Thus the normalized strong and auxiliary equations hold, and

    c(Tf-1)-pf^2=of-c=V.

For the ordinary candidate, use iO=Delta*iN instead. Then
(iO*c^2)^2=Delta*(f^2-1)=S^2, so its strong and auxiliary equations
also hold with the same f,T,V,y. Therefore these equations by themselves
do not remove the scaled first-index obstruction.

This construction follows the algebra of the primary normalized85 and
fixed-minus parent proofs linked in PROOF.md. It invokes no full parent
zero theorem and does not construct its missing index coordinate.

## 5. Remaining obstacle

A genuine counterexample still requires the same p to equal the exact
paid mask-packing expression using actual compiler numerals, a positive
transport quotient, and the full input norm with its shared rho split.
No tuple satisfying those conditions is claimed. Conversely, a sound
deletion proof must exploit some of that retained structure; the scaled
first/main/auxiliary subsystem and scalar size bounds are insufficient.
