# A simpler independent inner family: powers of 17

This preserves the older power-of-11 family and its audit. It is a simpler **inner-kernel** construction and still does not prove a full positive zero on a genuine compiler slice or a false accepted ordinary input.

Let j>=0 and set

    u=17^(2j), p=35u, n=30u, R=60u-1,
    X=2^p, Y=2^(7u-1), E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1,
    D=chi_A(p), c=psi_A(p), tau=chi_P(n), k=2psi_P(n).

The first and main norms hold exactly. The resonance identity is

    (2XY)^(p-1)=2Y*(4XY^2)^(n-1),

because p(p-n)=(7u)(2n-p). The same explicit Pell bounds as in PROOF.md give

    0<c/k-Y<4pY/X=70u*2^(-28u)<1.

Thus eta=c-kY and zeta=k-eta are strictly positive. Since P=1 modulo E and 2n=R+1,

    h=(k-R-1)/E

is a strictly positive integer. The index factor is 1, and p differs from R. The main projection gamma=(chi_A(p)-a*psi_A(p)-X)/H is a positive integer by the same elementary recurrence proof. Input loading at any fixed odd I>=3 is possible once p>I, using the unchanged formulas in PROOF.md Section3.

## Elementary coprimality

Since 17^2=1 modulo24, one has u=1 modulo24. The exact expression

    A=2^(42u-1)+2^(7u-1)+2

therefore gives

    A=3 modulo5, A=0 modulo7, A=0 modulo17.

Modulo5, the psi recurrence has coefficient 2A=1 and the period-six list 0,1,1,0,-1,-1. Since p=35u=5 modulo6, c=-1 modulo5. Modulo7 and17, the recurrence has coefficient0. Since p=3 modulo4, c=-1 modulo7 and17. The only possible prime divisors of p are 5,7,17. Consequently

    gcd(c,p)=1

for every j, without a fundamental-unit or Frobenius argument.

## An even simpler auxiliary extension

Here p=3 modulo4 always, so one can use

    f=D=chi_A(p), S=Delta*c.

Then Ns=Delta, c|S, f^2=1 modulo c, and gcd(c,f)=1. Choose a positive z with

    z=p modulo4p, z=R modulo c.

The CRT is compatible because gcd(c,p)=1. It gives z=3 modulo4. The quadratic-ring identity at f=chi_A(p) gives (chi_A(4p),psi_A(4p))=(1,0) modulo f. With

    V=chi_S(z)/S, y=psi_S(z),
    T=(V+c+R*f^2)/(c*f),

the same odd-quotient identities give V=-c modulo f and V=-R modulo c. Hence T is a positive integer, the literal V=c(Tf-1)-Rf^2 holds, and Na=1. The forced inverse of the deleted row is now simply

    i=S/(Delta*c^2)=1/c,

which is nonintegral. Every inner norm/index equation and the main projection hold, with p=35u different from the packed-index target R=60u-1.

## Exact unresolved compiler interface

Apply PROOF.md Section4 verbatim with the replacements

    u=17^(2j), p=35u, R=60u-1, Y exponent=7u-1.

In particular choose q=B^N=2^t with 3t<=7u-1, preserve every genuine fixed numeral and the ordinary input, and put J=(q-1)/(B-1), Q=q^2-1, M=(MC+q MF)J, e=p mod t, W=2^(ell*x+b). A full intended-factor completion requires and is supplied by

    R=M modulo Q,
    G=(R-M)/Q=q^2-Z-qF,
    F=(K+2^e)(W+Z) modulo q-1,
    F>=1, Z>=1, F+2Z+W+ell*x<q.

No such genuine completion is proved here. The larger Q modulus and transport obstruction to a naive prime-existence shortcut remain unchanged.

There is an immediate necessary constraint for this family. If N were even, d odd would give q=1 modulo3, Q=0 modulo3 and J=0 modulo3, hence the actual packed R=0 modulo3. But 60u-1=2 modulo3. Thus N must be odd. For odd N, q=2 and J=1 modulo3, so the genuine fixed source numerals must satisfy

    MC+2MF=2 modulo3.

This condition uses the shifted MF source port and must not be assumed automatically from the compiler recipe. Also if 3|N, then 7|J, requiring R=0 modulo7; since R=4*2^j-1 modulo7, this requires j=1 modulo3. These are restrictions on this family, not on every candidate zero.

For either family, alpha>=1 sharpens the generic packing lower bound to

    R >= [q*(W+ell*x+3)-1]*(q^2-1)+M.

Indeed G=q^2-qF-Z=(2q-1)Z+q(W+ell*x+alpha), and Z,alpha>=1. It prevents small inner fixtures from being mistaken for full compiler zeros. It does not prove nonexistence for later family members.
